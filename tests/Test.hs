-- Minimal demonstration of syb-with-class.  Here we have a class Size
-- with a base instance.  Then we override it for lists, and
-- demonstrate how gsize uses the list behavior on lists and the base
-- behavior otherwise.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -Wall #-}

import Data.Generics.SYB.WithClass.Basics (Data, gmapQ, Proxy)
import Data.Generics.SYB.WithClass.Context (Sat(dict))
import Data.Generics.SYB.WithClass.Instances ()
import Test.HUnit (assertEqual, Counts(..), runTestTT, showCounts, Test(TestCase))

class Size a where
    gsize :: a -> Int

-- Dictionary type and Sat instance
data SizeD a = SizeD { gsizeD :: a -> Int }

instance Size t => Sat (SizeD t) where
  dict = SizeD { gsizeD = gsize }

instance {-# OVERLAPPABLE #-} Data SizeD t => Size t where
  -- The base behavior of gsize for any instance of Data
  gsize t = 1 + sum (gmapQ (error "urk" :: Proxy SizeD) (gsizeD dict) t)

instance Size a => Size [a] where
  -- Override base gsize behavior for lists
  gsize [] = 0
  gsize (x:xs) = gsize x + gsize xs

main :: IO ()
main = do
  counts <- runTestTT (let expected = (2,1)
                           actual = (gsize ['a', 'b'], gsize 'x') in
                       TestCase (assertEqual "sample" expected actual))
  case counts of
    Counts {errors = 0, failures = 0} -> return ()
    _ -> error (showCounts counts)
