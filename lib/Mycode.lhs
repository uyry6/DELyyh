\section{Floyd–Warshall algorithm}
\label{sec:Floyd}
In this section, we give a Haskell implementation of the
Floyd–Warshall algorithm\cite{Floyd},
which is related to Kleene's algorithm\cite{Kleene}: an algorithm converting
DFA(deterministic finite automata) into RE(regular expressions).

The goal of this code is to find a shortest weighted path
between two vertices.

We start with the definition of graphs and give an example of a graph.
\begin{code}
module Mycode where

data Graph = Gr [Int] [(Int,Int)] ((Int,Int) -> Int)

instance (Show Graph) where
  show (Gr vertices edge weight) =
    "Gr " ++ show vertices ++ " " ++ show (zip edge (map weight edge))


myGraph :: Graph
myGraph = Gr vertices edge weight where
  vertices=[1,2,3,4]
  edge=[(1,3),(2,1),(4,2),(3,4),(2,3)]
  weight (1,3) = -2
  weight (2,1) = 4
  weight (4,2) = -1
  weight (3,4) = 2
  weight (2,3) = 3
  weight _     = 9999999999
\end{code}
%weight _     = 9999999999 -- use Infinity :: Fractional ?

Now we can give a \texttt{shortestPath} function, where the arguments are a graph,
the start vertex, the end vertex, and the intermediate vertex respectively.
If there is no intermediate vertex between the start vertex and the end vertex,
then the output equals the weight between these two vertexes;
if we take vertex $n$ as the intermediate vertex, the output equals the smaller
value of the output taking $n-1$ as the intermediate vertex or the summation of
the outputs taking $n-1$ as the intermediate vertex but $n$ as the new start
vertex or end vertex respectively.
In this example, if you take $4$ as the intermediate vertex, the function will
return the cost of the best-weighted path. For convenience, $9999999999$
means there is no such path between the vertices.

Then we define the \texttt{shortestPath} function as follows:
\begin{code}
shortestPath :: Graph -> Int -> Int -> Int -> Int
shortestPath (Gr _ _ weight) a b 0 = weight (a,b)
shortestPath g@Gr{}    a b c =
  minimum [ shortestPath g a b (c-1)
          , shortestPath g a c (c-1) + shortestPath g c b (c-1) ]
\end{code}

The example is as follows:
\begin{showCode}
*MyCode> myGraph
Gr [1,2,3,4] [((1,3),-2),((2,1),4),((4,2),-1),((3,4),2),((2,3),3)]
*MyCode> shortestPath myGraph 2 3 4
2
\end{showCode}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Next section
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Deterministic Finite automata}
In this section, we give a general method to produce DFA
and an implementation in Haskell.\cite{lipovaca2011learn}

First, we define a DFA\cite{DFA}.
A DFA is represented formally by a 5-tuple $(Q,\sum,q_0,F,\delta)$, where:
\begin{itemize}
  \item $Q$ : a fine set of states
  \item $\sum$ : a finite set of input symbols
  \item $q_0 \in Q$ : a start states
  \item $F \subseteq Q$ : a set of final state
  \item $\delta: Q \times \sum \rightarrow Q$ : a trasition function
\end{itemize}
The code is as follows:
\begin{code}
type Alphabet = String
type TransitionFunction = [((Int, Char), Int)]

data DFA = DFA{states :: [Int]
              ,alphabet :: Alphabet
              ,start :: Int
              ,finals :: [Int]
              ,trans :: TransitionFunction}
              deriving (Show)
\end{code}

DFA work as follows:

We input a string of symbols, for example, $``10100110"$,
from the start state. We take the first digit of the string, `$1$',
and the state $q_0$ as arguments for the function $\delta$ to get to another
state. The string becomes $``0100110"$ now. We repeat the procedure.
Once the string becomes $``$ $"$, the empty string, we check the state where it
stops. If the state is in the set of final(accepting) states, the string is
accepted; otherwise, it is rejected.

In this article, we only use `$0$',`$1$' as our symbols.
We define the accepting function as follows:
\begin{code}
acceptingInDFA :: DFA -> String -> Bool
acceptingInDFA (DFA _ _ s f t) = state s
  where  state q "" = q `elem` f
         state q ('1':xs) = state (t ! (q,'1')) xs
         state q ('0':xs) = state (t ! (q,'0')) xs
         state _ _ = error "unkonwn symbol"

(!) :: Eq a => [(a,b)] -> a -> b -- suggested by Malvin
(!) rel x = y where (Just y) = lookup x rel
\end{code}

Here are some examples of DFA and their diagrams:

\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto]
   \node[state,initial,accepting] (s_1)   {$s_1$};
    \path[->]
    (s_1) edge [loop above] node {0} ()
          edge [loop below] node {1} ();
\end{tikzpicture}

\begin{code}
exTrue :: DFA
exTrue = DFA q sig s f t where
          q   = [1]
          sig = ['0','1']
          s   = 1
          f   = [1]
          t   = [((1,'1'),1),((1,'0'),1)]
\end{code}

\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto]
   \node[state,initial] (s_1)   {$s_1$};
   \node[state,accepting] (s_2) [right=of s_1] {$s_2$};
    \path[->]
    (s_1) edge [bend left] node {0} (s_2)
          edge [loop above] node {1} ()
    (s_2) edge [bend left] node {1} (s_1)
          edge [loop right] node {0} ();
\end{tikzpicture}

\begin{code}
exEnd0 :: DFA
exEnd0 = DFA q sig s f t where
          q   = [1,2] -- HLint Suggestion: Reduce duplication.
          sig = ['0','1'] -- I want to keep them to make the example clear.
          s   = 1
          f   = [2]
          t   = [((1,'1'),1),((1,'0'),2),((2,'1'),1),((2,'0'),2)]
\end{code}

\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto]
   \node[state,initial,accepting] (s_1)   {$s_1$};
   \node[state] (s_2) [right=of s_1] {$s_2$};
    \path[->]
    (s_1) edge [bend left] node {0} (s_2)
          edge [loop above] node {1} ()
    (s_2) edge [bend left] node {0} (s_1)
          edge [loop right] node {1} ();
\end{tikzpicture}

\begin{code}
exWiki :: DFA
exWiki = DFA q sig s f t where
          q   = [1,2]
          sig = ['0','1']
          s   = 1
          f   = [1]
          t   = [((1,'1'),1),((1,'0'),2),((2,'1'),2),((2,'0'),1)]
\end{code}

\begin{tikzpicture}[shorten >=1pt,node distance=3cm,on grid,auto]
   \node[state,initial] (s_1)   {$s_1$};
   \node[state,accepting] (s_2) [right=of s_1] {$s_2$};
   \node[state,accepting] (s_3) [below=of s_1] {$s_3$};
   \node[state] (s_4) [below=of s_2] {$s_4$};
    \path[->]
    (s_1) edge node {1} (s_2)
          edge node {0} (s_3)
    (s_2) edge [bend left] node {0} (s_3)
          edge node {1} (s_4)
    (s_3) edge [bend left] node {1} (s_2)
          edge node {0} (s_4)
    (s_4) edge [loop right] node {0} ()
          edge [loop below] node {1} ();
\end{tikzpicture}

\begin{code}
ex01or10 :: DFA
ex01or10 = DFA q sig s f t where
          q   = [1..4]
          sig = ['0','1']
          s   = 1
          f   = [2,3]
          t   = [((1,'1'),2),((1,'0'),3),((2,'1'),4),((2,'0'),3),
                 ((3,'1'),2),((3,'0'),4),((4,'1'),4),((4,'0'),4)]
\end{code}

Some example of how the accepting function works:
\begin{showCode}
*MyCode> acceptingInDFA exTrue "1001110101"
True
*MyCode> acceptingInDFA exEnd0 "1001110101"
False
*MyCode> acceptingInDFA exEnd0 "10011101010"
True
*MyCode> acceptingInDFA exWiki "10011101010"
False
*MyCode> acceptingInDFA exWiki "100111010100"
True
*MyCode> acceptingInDFA ex01or10 "100111010100"
False
*MyCode> acceptingInDFA ex01or10 "010101"
True
*MyCode> acceptingInDFA ex01or10 "10101010"
True
\end{showCode}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Next section
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Regular expressions to finite automata}
In this section, we give a converting algorithm from RE
to NFA(non-deterministic finite automaton), and from
NFA to DFA. We use NFA only as an intermediate step.
\footnote{There are already algorithms for RE to NFA
and NFA to DFA. It will be more complicated if we skip
NFA and write our program for RE to DFA directly.}

First we define RE used in this article as follows:
\begin{itemize}
  \item The empty string $\epsilon$ and $0$ and $1$ are RE.
  \item For $\phi$ and $\psi$ are RE, $\phi^*$(Kleene star), $\phi\psi$(concatenation),
  and $\phi | \psi$(alternation) are RE.
\end{itemize}

An example for RE is $(01)^*|(10)^*|0(10)^*|1(01)^*$. Our goal is to get a function
that takes as input a regular expression and that outputs a DFA that accepts
the same regular expression.

\subsection{RE to NFA}
Now we want to convert RE to NFA.
We start from formal definiton of RE:\cite{RE}
\begin{itemize}
  \item (empty set) $\emptyset$
  \item (empty string) $\epsilon$
  \item (literal character) \texttt{'0','1'} in $\sum$
\end{itemize}

Operations:
\begin{itemize}
  \item (concatenation) $RS$
  \item (alternation) $R|S$
  \item (Kleene star) $R^*$
\end{itemize}

We take the following definition of \texttt{data Reg}
from the reference\cite{thompson2000regular}.\footnote{We only refer to
the definition of \texttt{Reg} and use a different way to program.}
\begin{code}
data Reg = E | -- Empty string
           L Char | -- Literal
           Alt Reg Reg | -- alternation
           Con Reg Reg | -- Concatenation
           Kle Reg -- Kleene star
           deriving (Eq,Show)
\end{code}

Some exaples for RE are:
\begin{code}
exRE1 :: Reg
exRE1 = Alt (L '1') (Con (L '1') (L '0')) -- 1|10

exRE2 :: Reg
exRE2 = Alt (Con (L '0') (L '0')) (Con (L '1') (L '0')) -- 00|10

exRE3 :: Reg
exRE3 = Alt (L '1') (Con (L '1') (Alt (L '1') (L '0'))) -- 1|(1(1|0))

exRE4 :: Reg
exRE4 = Kle (L '1') -- 1*

exRE5 :: Reg
exRE5 = Kle (Con exRE1 exRE2) -- ((1|10)(00|10))*
\end{code}

Then we define NFA\cite{NFA}, which can access a set of states
instead of one state in DFA.
An NFA is represented formally by a 5-tuple $(Q,\sum,q_0,F,\Delta)$, where:
\begin{itemize}
  \item $Q$ : a fine set of states
  \item $\sum$ : a finite set of input symbols
  \item $q_0 \in Q$ : a start state
  \item $F \subseteq Q$ : a set of final state
  \item $\Delta: Q \times \sum \rightarrow P(Q)$ : a transition function
\end{itemize}


\begin{code}

type NTransitionFunction = [((Int, Char), [Int])]

data NFA = NFA{n_states :: [Int]
              ,n_alphabet :: Alphabet
              ,n_start :: Int
              ,n_finals :: [Int]
              ,n_trans :: NTransitionFunction}
              deriving Show
\end{code}

In this section, we use Thompson's construction\cite{aho2003compilers} algorithm
to construct NFA from RE.
For $1^*$, the NFA is the following.
\begin{code}
onestar :: NFA
onestar = NFA nq nsig ns nf nt where
  nq   = [1..4]
  nsig = ['e','0','1']
  ns   = 1
  nf   = [4]
  nt  = [((1,'e'),[1,2,4]),((2,'1'),[3]),((2,'e'),[2])
        ,((3,'e'),[2,3,4]),((4,'e'),[2,4])]
\end{code}

Before we define the function \texttt{regToNFA}, we define some function
we will use in defining \texttt{regToNFA}.
The function \texttt{replace'} replaces states in transition function.
\begin{code}
replace' :: Eq a => a -> a -> [a] -> [a]
replace' x y = map (\z -> if x == z then y else z)
\end{code}

The function \texttt{toSet} sends a list to a set;
the function \texttt{subset} checks subset relation.
\begin{code}
toSet :: Eq a => [a] -> [a]
toSet [] = []
toSet (x:xs) = x : toSet(filter (/= x) xs)

subset :: Eq a => [a] -> [a] -> Bool
subset a b = null [x | x<-a ,x `notElem` b]
\end{code}

Here is RE to NFA\cite{REtoNFA_YT}\cite{Replace}. We begin from define empty
set and literals.
\begin{code}
regToNFA :: Reg -> NFA
regToNFA E = NFA nq nsig ns nf nt where
  nq   = [1,2]
  nsig = ['e','0','1']
  ns   = 1
  nf   = [2]
  nt   = [((1,'e'),[2])]
regToNFA (L '1') = NFA nq nsig ns nf nt where
  nq   = [1,2]
  nsig = ['e','0','1']
  ns   = 1
  nf   = [2]
  nt   = [((1,'1'),[2])]
regToNFA (L '0') = NFA nq nsig ns nf nt where
  nq   = [1,2]
  nsig = ['e','0','1']
  ns   = 1
  nf   = [2]
  nt   = [((1,'0'),[2])]
regToNFA (L  _ ) = error "unkonwn symbol"
\end{code}

Then we define the operators \texttt{Con}, \texttt{Alt}, and \texttt{Kle} recursively.
Notice that we reassign states in transition functions.
\begin{code}
regToNFA (Con E y) = regToNFA y
regToNFA (Con x E) = regToNFA x
regToNFA (Con x y) = NFA nq nsig ns nf nt where
  nq   = [1..(lengthX + lengthY - 1)]
  nsig = ['e','0','1']
  ns   = 1
  nf   = [length nq]
  nt   = n_trans regToNFAX ++
         map (\((a,b),c)->((a+lengthX-1,b),map (\n->n+lengthX-1) c))(n_trans regToNFAY)
  lengthX = length(n_states regToNFAX)
  lengthY = length(n_states regToNFAY)
  regToNFAX = regToNFA x
  regToNFAY = regToNFA y
regToNFA (Alt x y)
  |x == y    = regToNFA x
  |otherwise = NFA nq nsig ns nf nt where
  nq   = [1..(lengthX + lengthY - 2)]
  nsig = ['e','0','1']
  ns   = 1
  nf   = [length nq]
  nt   = map (\((a,b),c)->((a,b),map (\n->n+lengthX-2) c))headRegToNFAY ++
         zip fstRegToNFAX (map replace'' sndRegToNFAX) ++
         map (\((a,b),c)->((a+lengthX-2,b),map (\n->n+lengthX-2) c))tailRegToNFAY
  lengthX = length(n_states regToNFAX)
  lengthY = length(n_states regToNFAY)
  regToNFAX = regToNFA x
  regToNFAY = regToNFA y
  headRegToNFAY = [head (n_trans regToNFAY)]
  tailRegToNFAY = tail (n_trans regToNFAY)
  fstRegToNFAX  = map fst (n_trans regToNFAX)
  sndRegToNFAX  = map snd (n_trans regToNFAX)
  replace'' = replace' lengthX (length nq)
regToNFA (Kle E) = regToNFA E
regToNFA (Kle x) = NFA nq nsig ns nf nt where
  nq   = [1..(lengthX + 2)]
  nsig = ['e','0','1']
  ns   = 1
  nf   = [length nq]
  nt   = [((1,'e'),[2]),((1,'e'),[lengthX+2])] ++
         map (\((a,b),c)->((a+1,b),map (+ 1) c))(n_trans regToNFAX) ++
         [((lengthX+1,'e'),[lengthX+2]),((lengthX+2,'e'),[2])]
  lengthX = length(n_states regToNFAX)
  regToNFAX = regToNFA x
\end{code}

Here is an example of how reToNFA works:
\begin{showCode}
*Mycode> exRE1
Alt (L '1') (Con (L '1') (L '0'))
*MyCode> regToNFA exRE1
NFA {n_states = [1,2,3], n_alphabet = "e01", n_start = 1, n_finals = [3],
n_trans = [((1,'1'),[3]),((1,'1'),[2]),((2,'0'),[3])]}
\end{showCode}
This only represents arrows on the diagram below.

\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto]
   \node[state,initial] (s_1)   {$s_1$};
   \node[state] (s_2) [right=of s_1] {$s_2$};
   \node[state,accepting] (s_3) [below=of s_2] {$s_3$};
    \path[->]
    (s_1) edge node {1} (s_3)
          edge node {1} (s_2)
    (s_2) edge node {0} (s_3);
\end{tikzpicture}

Notice that every state can transit from itself to itself with `$e$'.
And we can combine arrows $((1,\mbox{`}1\mbox{'}),[2])$ and $((1,\mbox{`}1\mbox{'}),[3])$
to $((1,\mbox{`}1\mbox{'}),[2,3])$.
First, We combine $((x,\mbox{`}y\mbox{'}),[z])$
and $((x,\mbox{`}y\mbox{'}),[w])$ to $((x,\mbox{`}y\mbox{'}),[z,w])$:
\begin{code}
combineNTrans :: NTransitionFunction -> NTransitionFunction
combineNTrans x
  |length x>1 = head (com x) : combineNTrans(tail (com x))
  |otherwise = x

com :: NTransitionFunction -> NTransitionFunction
com x
  |length x < 2 = x
  |fst (head x) `elem` map fst (tail x)
  = toSet(com( (fst (head x),toSet(snd (head x)
    ++ concatMap snd (filter (\n -> fst n == fst (head x))
    (tail x) ) ))
    : filter (\n -> fst n /= fst (head x))(tail x) ) )
  |otherwise = x
\end{code}

Here are some examples for test:
\begin{code}
exNTF :: NTransitionFunction
exNTF = [((1,'e'),[2,8]),((1,'e'),[4,3]),((3,'0'),[4]),((4,'0'),[5])
      ,((5,'0'),[7]),((5,'1'),[6]),((6,'0'),[7]),((6,'0'),[8])
      ,((8,'e'),[2])]

exNTF2 :: NTransitionFunction
exNTF2 = [((1,'e'),[2,8]),((1,'e'),[9])]
\end{code}

This example shows how \texttt{combineNTrans} works:
\begin{showCode}
*MyCode> combineNTrans exNTF
[((1,'e'),[2,8,4,3]),((3,'0'),[4]),((4,'0'),[5]),((5,'0'),[7])
,((5,'1'),[6]),((6,'0'),[7,8]),((8,'e'),[2])]
*Mycode> combineNTrans exNTF2
[((1,'e'),[2,8,9])]
\end{showCode}

However, \texttt{regToNFA} is not enough for the powerset construction\cite{PFA},
because it lacks reflexivity for `$e$'. Therefore, we need \texttt{regToNFA'},
which has reflexivity.
We want to add transition functions $((x,\mbox{`}e\mbox{'}),[x])$,
which is reflexivity, to the original NFA.
We divide the process into two parts. The first part adds `$e$' to the states
which already has `$e$' to some other states to themselves:
\begin{code}
addE :: ((Int, Char), [Int]) -> ((Int, Char), [Int])
addE ((x,'e'),z) = ((x,'e'),x : z)
addE x = x
\end{code}

The result looks like:
\begin{showCode}
*MyCode> map addE (combineNTrans exNTF)
[((1,'e'),[1,2,8,4,3]),((3,'0'),[4]),((4,'0'),[5]),((5,'0'),[7])
,((5,'1'),[6]),((6,'0'),[7,8]),((8,'e'),[8,2])]
\end{showCode}


The second part adds `$e$' to the reminded states to themselves:
\begin{code}
remainsE :: [Int] -> NTransitionFunction -> NTransitionFunction
remainsE q n = n ++ [((x,'e'),[x])|x<-q, (x,'e') `notElem` map fst n]
\end{code}

Result looks like:
\begin{showCode}
*MyCode> remainsE [1..8] (map addE (combineNTrans exNTF))
[((1,'e'),[1,2,8,4,3]),((3,'0'),[4]),((4,'0'),[5]),((5,'0'),[7])
,((5,'1'),[6]),((6,'0'),[7,8]),((8,'e'),[8,2]),((2,'e'),[2])
,((3,'e'),[3]),((4,'e'),[4]),((5,'e'),[5]),((6,'e'),[6]),((7,'e'),[7])]
\end{showCode}

Now combine all funcitons to get our final \texttt{regToNFA'} function:
\begin{code}
regToNFA' :: Reg -> NFA
regToNFA' x = NFA nq nsig ns nf nt' where
  NFA nq nsig ns nf nt = regToNFA x
  nt' = remainsE nq (map addE (combineNTrans nt))
\end{code}

Final result looks like:
\begin{showCode}
*MyCode> regToNFA' exRE5
NFA {n_states = [1,2,3,4,5,6,7,8], n_alphabet = "e01",
n_start = 1, n_finals = [8],
n_trans = [((1,'e'),[1,2,8]),((2,'1'),[4,3]),((3,'0'),[4])
,((4,'0'),[5]),((5,'0'),[7]),((5,'1'),[6]),((6,'0'),[7])
,((7,'e'),[7,8]),((8,'e'),[8,2]),((2,'e'),[2]),((3,'e'),[3])
,((4,'e'),[4]),((5,'e'),[5]),((6,'e'),[6])]}
\end{showCode}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Next section
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\subsection{NFA to DFA - powerset construction}

Now we are going to convert NFA to DFA
by using the powerset construction.
In this section, PFA means a DFA constructed by powerset construction.
PFA is basically a special case of DFA, which has sets of states from NFA
as its states.
We defint the data for PFA:
\begin{code}
type PTransitionFunction = [(([Int], Char), [Int])]

data PFA = PFA{p_states :: [[Int]]
              ,p_alphabet :: Alphabet
              ,p_start :: [Int]
              ,p_finals :: [[Int]]
              ,p_trans :: PTransitionFunction}
              deriving Show
\end{code}

To get \texttt{nfaToPFA}, we need some fucntions below.
Combining these functions, we can get the states for PFA,
which are in the form $[[a,...,b],...,[c,...,d]]$.
\begin{code}
nexte :: Int -> NTransitionFunction -> [Int] --'e'
nexte a ntf
  |(a,'e') `elem` map fst ntf = ntf ! (a,'e')
  |otherwise  = []

next1 :: Int -> NTransitionFunction -> [Int] --'1'
next1 a ntf
  |(a,'1') `elem` map fst ntf = ntf ! (a,'1')
  |otherwise  = []

next0 :: Int -> NTransitionFunction -> [Int] --'0'
next0 a ntf
  |(a,'0') `elem` map fst ntf =  ntf ! (a,'0')
  |otherwise  = []

ntT :: (Int -> NTransitionFunction -> [Int])
        -> [Int] -> NTransitionFunction -> [Int]
ntT t x ntf = nt_te where
  nte a = nexte a ntf
  tt  a = t a ntf
  nt_tn = toSet(concatMap nte (concatMap tt x))
  nt_te
    |subset (toSet(concatMap nte nt_tn)) nt_tn = nt_tn
    |otherwise = ntT nexte nt_tn ntf

pq :: [[Int]] -> NTransitionFunction -> [[Int]]
pq [[]] _ = [[]]
pq x ntf
  |subset (tS x ntf) x = toSet x
  |otherwise = toSet (tS x ntf ++ pq (x ++ tS x ntf) ntf)

tS :: [[Int]] -> NTransitionFunction -> [[Int]]
tS x ntf  = toSet (map nt_t1 x ++ map nt_t0 x) where
  nt_t1 s = ntT next1 s ntf
  nt_t0 s = ntT next0 s ntf
\end{code}

Now we can get the transition map from
a state to another state.(The most important part.)
And therefore get the \texttt{nfaToPFA} function.
\begin{code}
nfaToPFA :: NFA -> PFA
nfaToPFA (NFA _ _ _ nf nt) = PFA p_q sig p_s p_f p_t where
  p_q = pq [start1] nt
  sig = ['0','1']
  p_s = start1
  p_f = [xf | xf <- p_q, (\ [x] -> x) nf `elem` xf]
  p_t = [((x,'1'),ntT next1 x nt) | x <- p_q]
        ++ [((x,'0'),ntT next0 x nt) | x <- p_q]
  start1 = ntT nexte [1] nt
\end{code}

The results looks like:
\begin{showCode}
*MyCode> nfaToPFA (regToNFA' exRE4)
PFA {p_states = [[3,4,2],[],[1,2,4]], p_alphabet = "01"
, p_start = [1,2,4], p_finals = [[3,4,2],[1,2,4]]
, p_trans = [(([3,4,2],'1'),[3,4,2]),(([],'1'),[])
,(([1,2,4],'1'),[3,4,2]),(([3,4,2],'0'),[]),(([],'0'),[])
,(([1,2,4],'0'),[])]}
\end{showCode}

Finally we give a function to implement NFA.
It is identical to the fucntion for DFA:
\begin{code}
acceptingInPFA :: PFA -> String -> Bool
acceptingInPFA (PFA _ _ s f t) = state s
  where  state q "" = q `elem` f
         state q ('1':xs) = state (t ! (q,'1')) xs
         state q ('0':xs) = state (t ! (q,'0')) xs
         state _ _ = error "unkonwn symbol"
\end{code}



\begin{code}
exRE6 :: Reg
exRE6 = Alt zero1 one0 where
  zero1  = Kle (Con (L '0') (L '1'))
  one0   = Kle (Con (L '1') (L '0'))
\end{code}

Some result:
\begin{showCode}
*MyCode> acceptingInPFA (nfaToPFA (regToNFA' exRE6)) "01010101"
True
*MyCode> acceptingInPFA (nfaToPFA (regToNFA' exRE6)) "1010101010"
True
\end{showCode}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Next section
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Future work}
In this article, we only use `$0$' and `$1$' as our working symbols.
It is left to generalize our working symbols to arbitrary many symbols.
We only finished one direction that converts RE to NFA to DFA.
The other direction, DFA to RE, needs more works to accomplish.
PFA to simple DFA(with integers as states) is also a task which needs
some extra work. This article lacks an Arbitrary instance for QuickCheck
and can be added after.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%Working space only
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{comment}

This part is unused code. Leave them here for references.
====================================================================

instance (Show DFA) where
  show (DFA q sig s f t) =
    "DFA" ++ " {states = " ++ (show q) ++ ", " ++ "alphabet = " ++
    (show sig) ++ ", " ++ "start = " ++ (show s) ++ ", " ++ "finals = "
    ++ (show f) ++ ", " ++ "trans = " ++ (show t) ++ "}"

====================================================================

alwaystrue :: [Char] -> Bool
alwaystrue x = state1 x
  where state1 "" = True
        state1 y = state1 (tail y)

====================================================================

simpleDFA :: [Char] -> Bool
simpleDFA x = state1 x
  where state1 "" = True
        state1 ('1':xs) = state1 xs
        state1 xs       = state2 (tail xs)
        state2 "" = False
        state2 ('1':xs) = state2 xs
        state2 xs       = state1 (tail xs)

=====================================================================

zero1or1zero :: [Char] -> Bool
zero1or1zero x = state1 x
  where state1 "" = False
        state1 ('1':xs) = state2 xs
        state1 xs       = state3 (tail xs)
        state2 "" = True
        state2 ('1':xs) = state4 xs
        state2 xs       = state3 (tail xs)
        state3 "" = True
        state3 ('1':xs) = state2 xs
        state3 xs       = state4 (tail xs)
        state4 "" = False
        state4 ('1':xs) = state4 xs
        state4 xs       = state4 (tail xs)
{- old code example:
        state2 x
             |digitToInt(head x) == 1 = state4 (tail x)
             |otherwise = state3 (tail x)
-}

=======================================================================

{-
regToDFA :: Reg -> DFA
regToDFA E = DFA q sig s f t where
  q   = [1,2]
  sig = ['0','1']
  s   = 1
  f   = [1]
  t   = [((1,'1'),2),((1,'0'),2),((2,'1'),2),((2,'0'),2)]
regToDFA (L '1') = DFA q sig s f t where
  q   = [1,2,3]
  sig = ['0','1']
  s   = 1
  f   = [3]
  t   = [((1,'1'),3),((1,'0'),2),((2,'1'),2),((2,'0'),2)
        ,((3,'1'),2),((3,'0'),2)]
regToDFA (L '0') = DFA q sig s f t where
  q   = [1,2,3]
  sig = ['0','1']
  s   = 1
  f   = [3]
  t   = [((1,'1'),2),((1,'0'),3),((2,'1'),2),((2,'0'),2)
        ,((3,'1'),2),((3,'0'),2)]

regToDFA (Alt x y) = DFA q sig s f t where [1..((length x) + (length y) - 1)]
                     ['0','1'] 1 [2]
                     [((1,'1'),3),((1,'0'),2),((2,'1'),3),((2,'0'),3)
                     ,((3,'1'),3),((3,'0'),3)]

regToDFA x = DFA q sig s f t where
  q   = [1,2]
  sig = ['0','1']
  s   = 1
  f   = [1]
  t   = [((1,'1'),1),((1,'0'),2),((2,'1'),2),((2,'0'),1)]

--dfaToReg :: DFA -> RegularExpression

concatenation_t :: Reg -> Reg -> TransitionFunction
concatenation_t E y = trans (regToDFA y)
concatenation_t x E = trans (regToDFA x)

-}

======================================================================

testt :: NTransitionFunction
testt = [((1,'e'),[1,2,8]),((2,'1'),[4,3])
        ,((3,'0'),[4]),((4,'0'),[5]),((5,'0'),[7])
        ,((5,'1'),[6]),((6,'0'),[7]),((7,'e'),[7,8])
        ,((8,'e'),[8,2]),((2,'e'),[2,7]),((3,'e'),[3,8])
        ,((4,'e'),[4]),((5,'e'),[5]),((6,'e'),[6])]

===============
|[a] == (nexte a ntf) = [a]
|otherwise = (nexte a ntf) ++ nte (nexte a ntf)



fufu :: NTransitionFunction
fufu  = [((1,'e'),[1,2,5]),((2,'1'),[3]),((3,'0'),[4]),((4,'e'),[4,5])
,((5,'e')
,[5,2]),((2,'e'),[2]),((3,'e'),[3])]

\end{comment}


%ctrl+\ to kill program
