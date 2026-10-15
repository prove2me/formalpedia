-- Prove2me | Theorems.Thm_OAI_ParityWL_edgeTest_count
-- name    : OAI.ParityWL.edgeTest_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:47:33.739663+00:00
-- url     : https://prove2.me/theorems/2d9bed38-d866-4443-a512-e7a7bf36ac9e
-- title:
--   The edge test counts $1$ exactly when two root images are adjacent
-- statement:
--   Let $k\le t$ be natural numbers and $[k]=\{0,\dots,k-1\}$. A *rooted test* with $k$ roots and width $t$ is a finite set $P$ carrying a symmetric relation $R$ (loops allowed), a root map $\varrho\colon[k]\to P$ (not necessarily injective), and a rooted tree decomposition of $(P,R)$ (every element of $P$ lies in some bag, the bags containing a given element form a connected subtree, and every related pair lies in a common bag) whose bags have at most $t$ elements, in which every non-root bag shares fewer than $t$ elements with its parent bag and whose root bag is exactly $\varrho([k])$. For a graph $G$ on a finite vertex set $V$ and a tuple $x\in V^k$, the *count* of the test is the rational number
--   $$
--   \mathrm{cnt}_P(G,x)=\#\big\{f\colon P\to V\ :\ f(p)f(p')\in E(G)\text{ whenever }R(p,p'),\ \text{and } f(\varrho(i))=x_i\text{ for all } i\in[k]\big\}.
--   $$
--
--   For $i,j\in[k]$, the *edge test* $\mathsf{Ed}_{ij}$ has underlying set $[k]$ with the relation $R(p,p')\iff (p,p')\in\{(i,j),(j,i)\}$, the identity as root map, and the decomposition with a single bag.
--
--   **Theorem.** For every graph $G$ on a finite vertex set $V$ and every $x\in V^k$,
--   $$
--   \mathrm{cnt}_{\mathsf{Ed}_{ij}}(G,x)=\begin{cases}1,& x_ix_j\in E(G),\\ 0,& x_ix_j\notin E(G).\end{cases}
--   $$
--   In particular, for $i=j$ the count is $0$, since a simple graph has no loops.
--
--   The edge test realizes the adjacency bits of the atomic type of a tuple as a count function. Together with the equality test, it shows that the indicator functions of atomic types lie in the linear span of rooted-test counts.
--
--   **Formalization Note** `edgeTest hkt i j` is built with `singleBagTest` on `Fin k`; the hypothesis `hkt : k ≤ t` only ensures that the single bag has width at most $t$. `RootedTest.count` is the cardinality of the type of admissible maps `Maps G x`, cast to the rationals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean#L63-L89

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {k t : ℕ}

theorem OAI.ParityWL.edgeTest_count (hkt : k ≤ t) (i j : Fin k) {V : Type} [Fintype V]
    (G : SimpleGraph V) (x : Fin k → V) :
    (edgeTest hkt i j).count G x = if G.Adj (x i) (x j) then 1 else 0 := by sorry
