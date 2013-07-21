import Control.Monad
import Data.List
import Data.Maybe
import Debug.Trace
import Test.QuickCheck
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.IO
import System.Environment

data Vector a = Vector {
  from  :: Int,
  to    :: Int,
  elems :: [a]
} deriving Show

infixl 6 <+>

a <+> b =
  Vector {
    from = if from a /= from b then min (from a) (from b) else calcFrom xorElems,
    to   = if to a /= to b then max (to a) (to b) else calcTo xorElems,
    elems = xorElems
  }
    where
      xorElems = map (\(x,y)->x/=y) $ zip (elems a) (elems b)

calcFrom elems = length $ takeWhile not elems
calcTo   elems = length elems - (length $ takeWhile not $ reverse elems)

leftN n leader vects =
  map (\v -> if from v == n then v <+> leader else v) vects

data Matrix = Matrix { matrixLength :: Int, matrixVects :: [Vector Bool] }

instance Show Matrix where
  show (Matrix _ lst) =
    concat $ map ((++"\n") . (concat . map (show . \b->if b then 1 else 0)) . elems) lst

selectLeader n (Matrix _ vects) = do
  l <- listToMaybe $ filter (\(_, v) -> from v == n) $ zip [0..] vects
  return (snd l, map snd $ filter (\p -> fst p /= fst l) $ zip [0..] vects)

left n matrix@(Matrix l vects) =
  case selectLeader n matrix of
    Nothing -> if n > l then matrix else left (n+1) matrix
    (Just (leader, others)) -> Matrix l $ leader : matrixVects (left (n+1) (Matrix l (leftN n leader others)))

repFun 0 f =
  id
repFun n f =
  f . repFun (n-1) f

right matrix@(Matrix l vects) =
  Matrix l $ head vects : snd (mapAccumL (\a x ->
    if to a /= to x
    then
      (x, x)
    else
      (a, x<+>a)
  ) (head vects) (tail vects))

minimize matrix@(Matrix l _) =
  Matrix l . sortBy (\x y -> compare (from x) (from y)) . matrixVects . repFun l (right . Matrix l . sortBy (\x y -> compare (to y, from y) (to x, from x)) . matrixVects) $ left 0 matrix

stateBits matrix =
  map (\n -> map (\v -> from v < n && to v > n) vects) [0..l]
    where
      (Matrix l vects) = minimize matrix

states matrix =
  concat $ zipWith (\i l -> zip (repeat i) l) [0..] (map (sequence . map vary) $ stateBits matrix)

vary f = if f then [False, True] else [False]

transitionLayer common plus minus = do
  common' <- sequence $ map vary common
  plus'   <- sequence $ map vary plus
  minus'  <- sequence $ map vary minus
  return $ (map (uncurry (||)) (zip common' minus'), map (uncurry (||)) (zip common' plus'))

enLab' cols singles trans =
  concat $ map (\tr@((n, input1), (_, input2)) -> 
    if n `elem` singles 
    then
      [(tr, False),(tr, True)]
    else
      [(tr, xor $ map (uncurry (&&)) $ zip (map (uncurry (||)) $ zip input1 input2) (cols !! n))]
  ) trans


enLab _ [tr] =
  [(tr, False),(tr, True)]
enLab cols trans =
  map (\tr@((n, input1), (_, input2)) -> (tr, xor $ map (uncurry (&&)) $ zip (map (uncurry (||)) $ zip input1 input2) (cols !! n))) trans

transitions matrix =
  concat labs
    where
      (Matrix l vects) = minimize matrix
      stBits = stateBits matrix
      pairs  = zip stBits $ tail stBits
      common = map (map (uncurry (&&)) . uncurry zip) pairs
      plus   = map (map (\(x, y) -> not x && y) . uncurry zip) pairs
      minus  = map (map (\(x, y) -> x && not y) . uncurry zip) pairs
      trans  = map (\(n,c,p,m) -> map (\(a,b) -> ((n,a),(n+1,b))) $ transitionLayer c p m) $ zip4 [0..] common plus minus
      cols   = transpose $ map elems vects
      singles= concat $ map (\v -> if to v - from v == 1 then [from v] else []) vects
      labs   = map (enLab' cols singles) trans

mkTrellis :: Matrix -> Gr (Int, [Bool]) Bool
mkTrellis matrix =
  mkGraph sts'' trans'
    where
      sts    = states matrix
      trans  = transitions matrix
      sts'   = zip sts [0..]
      sts''  = zip [0..] sts
      trans' = map (\((from,to),lab) -> (fromJust $ lookup from sts', fromJust $ lookup to sts',lab)) trans

xor = foldl (/=) False

assert True  t =
  t
assert False _ =
  error "Assertion failed"

readMatrix bits =
  assert (maxlen == minlen) $
    Matrix maxlen $ map (\elems -> Vector (calcFrom elems) (calcTo elems) elems) bits
      where
        lens = map length bits
        maxlen = maximum lens
        minlen = minimum lens

genMatrix n m =
  vectorOf n (vector m)

prop1 matrix =
  (length m' == length (nub (map from m'))) && (length m' == length (nub (map to m')))
    where
      (Matrix l m) = minimize (readMatrix matrix)
      m' = filter (\v -> to v /= 0) m

checkMinimize = do
  quickCheck (forAll (genMatrix 1 1) prop1)
  quickCheck (forAll (genMatrix 2 2) prop1)
  quickCheck (forAll (genMatrix 3 3) prop1)
  quickCheck (forAll (genMatrix 3 10) prop1)
  quickCheck (forAll (genMatrix 10 3) prop1)
  quickCheck (forAll (genMatrix 19 17) prop1)
  quickCheck (forAll (genMatrix 17 19) prop1)

dotParams = nonClusteredParams {
  globalAttributes = [GraphAttrs [RankDir FromLeft]],
  fmtEdge =
    \(node1, node2, b) -> 
      if b then
        [Color [WC (X11Color Red) Nothing]]
      else
        [Style [SItem Dashed []], Color	[WC (X11Color Blue) Nothing]],
  fmtNode =
    \(node, t) ->
      [Label $ StrLabel $ Lazy.pack ""]
}

defaultVis :: (Graph gr) => gr (Int, [Bool]) Bool -> DotGraph Node
defaultVis = graphToDot dotParams

printTrellis :: Gr (Int, [Bool]) Bool -> Lazy.Text
printTrellis trellis =
  printDotGraph $ defaultVis trellis

printDotFile =
  Data.Text.Lazy.IO.writeFile

printMatrixTrellisFile filename =
  printDotFile filename . printTrellis . mkTrellis

readMat = do
  str <- getLine
  if str == [] then return [] else do
    next <- readMat
    return $ [map (\x->case x of '0'->False; '1'-> True) str] ++ next

main = do
  filename <- getArgs
  matrix <- readMat
  printMatrixTrellisFile (head filename) (readMatrix matrix)
  
