{-# LANGUAGE TemplateHaskell, CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
-- We can't warn about missing sigs as we have a group of decls in
-- quasi-quotes that we're going to put in a class instance

--
-- Ulf Norell, 2004
-- Started this module.
--
-- Sean Seefried, 2004
-- Extension for data definitions with type variables; comments added.
-- http://www.haskell.org/pipermail/template-haskell/2005-January/000393.html
--
-- Simon D. Foster, 2004--2005
-- Extended to work with SYB3.
--
-- Ralf Lammel, 2005
-- Integrated with SYB3 source distribution.
--

module Data.Generics.SYB.WithClass.Derive where

import Language.Haskell.TH
import Data.List
import Data.Char
import Control.Monad
import Data.Maybe
import Data.Generics.SYB.WithClass.Basics

-- maximum type paramters for a Typeable instance
maxTypeParams :: Int
maxTypeParams = 7


--
-- | Takes the name of an algebraic data type, the number of type parameters
--   it has and creates a Typeable instance for it.
deriveTypeablePrim :: Name -> Int -> Q [Dec]
deriveTypeablePrim name nParam
#ifdef __HADDOCK__
 = undefined
#else
  | nParam <= maxTypeParams =
     sequence
      [ instanceD (return [])
         (conT typeableName `appT` conT name)
        [ funD typeOfName [clause [wildP] (normalB
           [| mkTyConApp (mkTyCon $(litE $ stringL (nameBase name))) [] |]) []]
        ]
      ]
  | otherwise = error ("Typeable classes can only have a maximum of " ++
                      show maxTypeParams ++ " parameters")
  where
    typeableName
      | nParam == 0 = mkName "Typeable"
      | otherwise   = mkName ("Typeable" ++ show nParam)
    typeOfName
      | nParam == 0  = mkName "typeOf"
      | otherwise    = mkName ("typeOf" ++ show nParam)
#endif

--
-- | Takes a name of a algebraic data type, the number of parameters it
--   has and a list of constructor pairs.  Each one of these constructor
--   pairs consists of a constructor name and the number of type
--   parameters it has.  The function returns an automatically generated
--   instance declaration for the Data class.
--
--   Doesn't do gunfold, dataCast1 or dataCast2
deriveDataPrim :: Name -> [Type] -> [(Name, Int)] -> [(Name, [(Maybe Name, Type)])] -> Q [Dec]
deriveDataPrim name typeParams cons terms =
#ifdef __HADDOCK__
 undefined
#else
  do sequence (
      conDecs ++

      [ dataTypeDec
      , instanceD context (dataCxt myType)
        [ funD 'gfoldl
            [ clause ([wildP] ++ (map (varP . mkName) ["f", "z", "x"]))
                (normalB $ caseE (varE (mkName "x")) (map mkMatch cons))
                []
            ]
        , funD 'gunfold
          [clause ([wildP] ++ (map (varP. mkName) ["k", "z", "c"]))
            (if (null cons) then (normalB [| error "gunfold : Type has no constructors" |])
                            else (normalB $ caseE (varE (mkName "constrIndex") `appE` varE (mkName "c")) mkMatches)) []]
        , funD 'toConstr
            [ clause [wildP, varP (mkName "x")]
                (normalB $ caseE (varE (mkName "x"))
                 (zipWith mkSel cons conVarExps))
                []
            ]
        , funD 'dataTypeOf
            [ clause [wildP, wildP] (normalB $ varE (mkName theDataTypeName)) []
            ]
        ]
      ])
     where
         types = filter (\x -> case x of (VarT _) -> False; _ -> True) $ map snd $ concat $ map snd terms
         fieldNames = let fs = map (map fst.snd) terms in
                          map (\x -> if (null x || all isNothing x) then [] else map (maybe "" show) x) fs
         nParam = length typeParams

{-         paramNames = take nParam (zipWith (++) (repeat "a") (map show [0..]))
         typeQParams = map (\nm -> varT (mkName nm)) paramNames-}
         myType = foldl AppT (ConT name) typeParams
         dataCxt typ = conT ''Data `appT` varT (mkName "ctx") `appT` return typ
         satCxt typ = conT ''Sat `appT` (varT (mkName "ctx") `appT` return typ)
         dataCxtTypes = nub (typeParams ++ types)
         satCxtTypes = nub (myType : types)
         context = cxt (map dataCxt dataCxtTypes ++ map satCxt satCxtTypes)

         -- Takes a pair (constructor name, number of type arguments) and
         -- creates the correct definition for gfoldl
         -- It is of the form z <constr name> `f` arg1 `f` ... `f` argn
         mkMatch (c,n) =
            do  vs <- mapM (\s -> newName s) names
                match   (conP c $ map varP vs)
                        (normalB $ foldl
                           (\e x -> (varE (mkName "f") `appE` e) `appE` varE x)
                                    (varE (mkName "z") `appE` conE c)
                                    vs
                        ) []
           where names = take n (zipWith (++) (repeat "x") (map show [0 :: Integer ..]))
         mkMatches = map (\(n, (cn, i)) -> match (litP $ integerL n) (normalB $ reapply (appE (varE $ mkName "k")) i (varE (mkName "z") `appE` conE cn)) []) (zip [1..] cons)
           where
           reapply _ 0 f = f
           reapply x n f = x (reapply x (n-1) f)
         lowCaseName = map toLower nameStr
         nameStr = nameBase name
         theDataTypeName = lowCaseName ++ "DataType"
         -- Creates dataTypeDec of the form:
         -- <name>DataType = mkDataType <name> [<constructors]
         dataTypeDec = funD (mkName theDataTypeName)
                       [clause []
                        (normalB
                         [| mkDataType nameStr $(listE (conVarExps)) |]) [] ]

         -- conVarExps is a [ExpQ]. Each ExpQ is a variable expression
         -- of form varE (mkName <con>Constr)
         numCons = length cons
         constrNames =
           take numCons (map (\i -> theDataTypeName ++ show i ++ "Constr") [1 :: Integer ..])
         conNames = map (nameBase . fst) cons
         conVarExps = map (varE . mkName) constrNames
         conDecs = zipWith3 mkConstrDec constrNames conNames fieldNames
          where
           mkConstrDec decNm conNm fieldNm =
             funD (mkName decNm)
                     [clause []
                        (normalB
                         [| mkConstr $(varE (mkName theDataTypeName)) conNm fieldNm
                            $(fixity conNm)
                         |]) []]

         fixity (':':_)  = [| Infix |]
         fixity _        = [| Prefix |]

         mkSel (c,n) e = match  (conP c $ replicate n wildP)
                         (normalB e) []
#endif

deriveMinimalData :: Name -> Int  -> Q [Dec]
deriveMinimalData name nParam  = do
#ifdef __HADDOCK__
 undefined
#else
   decs <- qOfDecs
   let listOfDecQ = map return decs
   sequence
     [ instanceD context
         (conT ''Data `appT` (foldl1 appT ([conT name] ++ typeQParams)))
         listOfDecQ ]

   where
     paramNames = take nParam (zipWith (++) (repeat "a") (map show [0 :: Integer ..]))
     typeQParams = map (\nm -> varT (mkName nm)) paramNames
     context = cxt (map (\typ -> conT ''Data `appT` typ) typeQParams)
     qOfDecs =
       [d| gunfold _ _ _ = error ("gunfold not defined")
           toConstr x    = error ("toConstr not defined for " ++
                              show (typeOf x))
           dataTypeOf x = error ("dataTypeOf not implemented for " ++
                            show (typeOf x))
           gfoldl _ z x = z x
        |]
#endif

{- instance Data NameSet where
   gunfold _ _ _ = error ("gunfold not implemented")
   toConstr x = error ("toConstr not implemented for " ++ show (typeOf x))
   dataTypeOf x = error ("dataTypeOf not implemented for " ++ show (typeOf x))
   gfoldl f z x = z x -}

typeInfo :: DecQ -> Q (Name, [Name], [(Name, Int)], [(Name, [(Maybe Name, Type)])])
typeInfo m =
     do d <- m
        case d of
           DataD {} ->
            return $ (simpleName $ name d, paramsA d, consA d, termsA d)
           NewtypeD {} ->
            return $ (simpleName $ name d, paramsA d, consA d, termsA d)
           _ -> error ("derive: not a data type declaration: " ++ show d)

     where
        consA (DataD _ _ _ cs _)    = map conA cs
        consA (NewtypeD _ _ _ c _)  = [ conA c ]
        consA d                     = error ("consA: Unexpected decl: " ++
                                             show d)

        paramsA (DataD _ _ ps _ _)    = ps
        paramsA (NewtypeD _ _ ps _ _) = ps
        paramsA d                     = error ("paramsA: Unexpected decl: " ++
                                               show d)

        termsA (DataD _ _ _ cs _)   = map termA cs
        termsA (NewtypeD _ _ _ c _) = [ termA c ]
        termsA d                    = error ("termsA: Unexpected decl: " ++
                                             show d)

        termA (NormalC c xs)        = (c, map (\x -> (Nothing, snd x)) xs)
        termA (RecC c xs)           = (c, map (\(n, _, t) -> (Just $ simpleName n, t)) xs)
        termA (InfixC t1 c t2)      = (c, [(Nothing, snd t1), (Nothing, snd t2)])
        termA (ForallC _ _ c)       = termA c

        conA (NormalC c xs)         = (simpleName c, length xs)
        conA (RecC c xs)            = (simpleName c, length xs)
        conA (InfixC _ c _)         = (simpleName c, 2)
        conA (ForallC _ _ c)        = conA c

        name (DataD _ n _ _ _)      = n
        name (NewtypeD _ n _ _ _)   = n
        name d                      = error $ show d

simpleName :: Name -> Name
simpleName nm =
   let s = nameBase nm
   in case dropWhile (/=':') s of
        []          -> mkName s
        _:[]        -> mkName s
        _:t         -> mkName t

--
-- | Derives the Data and Typeable instances for a single given data type.
--
deriveOne :: Name -> Q [Dec]
deriveOne n =
  do    info' <- reify n
        case info' of
           TyConI d -> deriveOneDec d
           _ -> error ("derive: can't be used on anything but a type " ++
                      "constructor of an algebraic data type")

deriveOneDec :: Dec -> Q [Dec]
deriveOneDec dec =
  do (name, param, ca, terms) <- typeInfo (return dec)
     t <- deriveTypeablePrim name (length param)
     d <- deriveDataPrim name (map VarT param) ca terms
     return (t ++ d)

deriveOneData :: Name -> Q [Dec]
deriveOneData n =
  do    info' <- reify n
        case info' of
           TyConI i -> do
             (name, param, ca, terms) <- typeInfo ((return i) :: Q Dec)
             d <- deriveDataPrim name (map VarT param) ca terms
             return d
           _ -> error ("derive: can't be used on anything but a type " ++
                      "constructor of an algebraic data type")


--
-- | Derives Data and Typeable instances for a list of data
--   types. Order is irrelevant. This should be used in favour of
--   deriveOne since Data and Typeable instances can often depend on
--   other Data and Typeable instances - e.g. if you are deriving a
--   large, mutually recursive data type.  If you splice the derived
--   instances in one by one you will need to do it in depedency order
--   which is difficult in most cases and impossible in the mutually
--   recursive case. It is better to bring all the instances into
--   scope at once.
--
--  e.g. if
--     data Foo = Foo Int
--  is declared in an imported module then
--     $(derive [''Foo])
--  will derive the instances for it
derive :: [Name] -> Q [Dec]
derive names = do
  decss <- mapM deriveOne names
  return (concat decss)


deriveDec :: [Dec] -> Q [Dec]
deriveDec decs = do
  decss <- mapM deriveOneDec decs
  return (concat decss)


deriveData :: [Name] -> Q [Dec]
deriveData names = do
  decss <- mapM deriveOneData names
  return (concat decss)

deriveTypeable :: [Name] -> Q [Dec]
deriveTypeable names = do
  decss <- mapM deriveOneTypeable names
  return (concat decss)

deriveOneTypeable :: Name -> Q [Dec]
deriveOneTypeable n =
  do    info' <- reify n
        case info' of
           TyConI i -> do
             (name, param, _, _) <- typeInfo ((return i) :: Q Dec)
             t <- deriveTypeablePrim name (length param)
             return t
           _ -> error ("derive: can't be used on anything but a type " ++
                       "constructor of an algebraic data type")


--
-- | This function is much like deriveOne except that it brings into
--   scope an instance of Data with minimal definitions. gfoldl will
--   essentially leave a data structure untouched while gunfoldl,
--   toConstr and dataTypeOf will yield errors.
--
--   This function is useful when you are certain that you will never
--   wish to transform a particular data type.  For instance you may
--   be transforming another data type that contains other data types,
--   some of which you wish to transform (perhaps recursively) and
--   some which you just wish to return unchanged.
--
--   Sometimes you will be forced to use deriveMinimalOne because you
--   do not have access to the contructors of the data type (perhaps
--   because it is an Abstract Data Type). However, should the
--   interface to the ADT be sufficiently rich it is possible to
--   define you're own Data and Typeable instances.
deriveMinimalOne :: Name -> Q [Dec]
deriveMinimalOne n =
  do    info' <- reify n
        case info' of
           TyConI i -> do
            (name, param, _, _) <- typeInfo ((return i) :: Q Dec)
            t <- deriveTypeablePrim name (length param)
            d <- deriveMinimalData name (length param)
            return $ t ++ d
           _ -> error ("deriveMinimal: can't be used on anything but a " ++
                       "type constructor of an algebraic data type")


deriveMinimal :: [Name] -> Q [Dec]
deriveMinimal names = do
   decss <- mapM deriveMinimalOne names
   return (concat decss)

