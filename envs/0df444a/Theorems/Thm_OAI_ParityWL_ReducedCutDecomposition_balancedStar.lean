-- Prove2me | Theorems.Thm_OAI_ParityWL_ReducedCutDecomposition_balancedStar
-- name    : OAI.ParityWL.ReducedCutDecomposition.balancedStar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:42:09.894273+00:00
-- url     : https://prove2.me/theorems/bd3bdba6-b339-4d02-abf5-6d119d3e134c
-- title:
--   Reduced tree-decomposition cuts yield a balanced star for every star-parity witness
-- statement:
--   Let $F$ be a graph on a finite set $W$ and $t\in\mathbb{N}$. A *reduced cut decomposition* $D$ of $F$ of width $t$ consists of finitely many nodes numbered $0,\dots,N-1$, one of them the root, a parent map with $\mathrm{par}(i)<i$ for every non-root node $i$, and for each node $i$ a *bag* $B_i\subseteq W$ and a *side* $Y_i\subseteq W$. Put $S_i=B_i\cap B_{\mathrm{par}(i)}$ and $R_i=W\setminus(S_i\cup Y_i)$, and for nodes $i,j$ let the *branch* $\mathrm{Br}_i(j)$ be $R_i$ if $j=i$ is not the root, $Y_j$ if $j\neq i$ is a non-root node with $\mathrm{par}(j)=i$, and $\emptyset$ otherwise. The axioms are:
--
--   1. $|B_i|\le t$ for every node $i$;
--   2. $|S_i|<t$ for every non-root node $i$;
--   3. $Y_i\cap S_i=\emptyset$ for every non-root node $i$;
--   4. for every non-root node $i$, every edge of $F$ from a vertex of $Y_i$ to a vertex outside $Y_i$ ends in $S_i$;
--   5. for every node $i$, the bag $B_i$ and the branches $\mathrm{Br}_i(j)$ ($j$ ranging over all nodes) are pairwise disjoint and cover $W$.
--
--   The *template graph* $T_t$ has vertex set $[t]\sqcup\mathcal{H}_t$, where $[t]=\{0,1,\dots,t-1\}$ is the set of *main vertices* and $\mathcal{H}_t$ is the set of *helper vertices* $h=(i,j;m)$ with $i<j$ in $[t]$ and $m\in[t]\setminus\{i,j\}$. Any two distinct main vertices are adjacent, each helper $(i,j;m)$ is adjacent exactly to the three main vertices $i$, $j$ and $m$, and no two helpers are adjacent. The *star parity* $\beta_t\colon[t]\sqcup\mathcal{H}_t\to\mathbb{F}_2$ takes the value $1$ at the main vertex $0$ and the value $0$ at every other template vertex. Let $a\colon F\to T_t$ be a graph homomorphism; $a(x)$ is the *type* of $x$. A *weighted witness* $w=(\lambda,\mu)$ for $(T_t,F,a,\beta_t)$ consists of vertex weights $\lambda\colon W\to\mathbb{F}_2$ and edge weights $\mu\colon W\times W\to\mathbb{F}_2$ such that $\mu(x,y)=\mu(y,x)$, $\mu(x,y)=0$ whenever $xy$ is not an edge of $F$, $\sum_{y\in W,\ a(y)=u}\mu(x,y)=\lambda(x)$ for every $x\in W$ and every neighbour $u$ of $a(x)$ in $T_t$, and $\sum_{x\in W}\lambda(x)\,\beta_t(a(x))=1$. For $Y\subseteq W$ and a template vertex $u$, the *mass* of type $u$ on $Y$ is $m_Y(u)=\sum_{x\in Y,\ a(x)=u}\lambda(x)$.
--
--   A *balanced star* for $w$ consists of a number $n$ of regions, a map $\rho\colon W\to\{\ast\}\sqcup\{0,\dots,n-1\}$ whose fibre $B=\rho^{-1}(\ast)$, the *bag*, has $|B|\le t$, and for each region $r<n$ a *separator* $S_r\subseteq B$ with $|S_r|<t$, such that, writing $Y_r=\rho^{-1}(r)$ for the $r$-th region: (i) every edge of $F$ from a vertex of $Y_r$ to a vertex outside $Y_r$ ends in $S_r$; (ii) for every main index $j\in[t]$ such that no vertex of $S_r$ has type $j$, the mass vanishes: $m_{Y_r}(j)=0$.
--
--   **Theorem.** Let $D$ be a reduced cut decomposition of $F$ of width $t$, let $w$ be a weighted witness for $(T_t,F,a,\beta_t)$, and suppose $t>0$. Then
--   $$
--   \text{there exists a balanced star for } w.
--   $$
--
--   Combined with the choice-extraction theorem, this shows that a star-parity witness pulled back to a graph with a reduced cut decomposition of width $t$ forces the underlying choice system to be successful; this is how bounded-width pattern graphs are handled.
--
--   **Formalization Note** `ReducedCutDecomposition F t` extends `RootedCuts W` (fields `nodes`, `root`, `parent`, `parent_lt`, `bag`, `side`) by the axioms above; $S_i$, $R_i$ and $\mathrm{Br}_i(j)$ are `separator`, `reverseSide` and `branch`. The parent of the root is irrelevant. `WeightedWitness T F a b` has fields `vertex` ($\lambda$), `edge` ($\mu$), `symmetric`, `supported`, `coordinate` and `odd`; `Bit` is `ZMod 2`. The conclusion is `Nonempty (BalancedStar w)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/DecompositionCuts.lean#L164-L221

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {W : Type} [Fintype W]
variable {F : SimpleGraph W} {t : ℕ}
variable {a : F →g template t}

theorem OAI.ParityWL.ReducedCutDecomposition.balancedStar (D : ReducedCutDecomposition F t)
    (w : WeightedWitness (template t) F a (starParity t)) (ht : 0 < t) :
    Nonempty (BalancedStar w) := by sorry
