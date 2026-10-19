-- Prove2me | Theorems.Thm_OAI_Barnette_Network_cap_coloring
-- name    : OAI.Barnette.Network.cap_coloring
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:03:41.286987+00:00
-- url     : https://prove2.me/theorems/44b7ff77-48a1-48d9-888b-cf6186cb5bc2
-- title:
--   Contracting one side of a 3-edge cut of a cubic bipartite network keeps a proper black–white coloring
-- statement:
--   A *network* $N$ consists of finite sets $V$ (vertices) and $E$ (edges) together with maps $t,h:E\to V$ giving the tail and the head of each edge; parallel edges and loops are allowed a priori. Its underlying simple graph $G(N)$ has an edge between $v\neq w$ whenever some $e\in E$ has endpoints $v$ and $w$. For $A\subseteq V$ write $\delta(A)$ for the set of edges with exactly one endpoint in $A$ and $R(A)$ for the set of edges with at least one endpoint in $A$.
--
--   Let $B\subseteq V$ be a set of *black* vertices such that every edge has exactly one black endpoint: $t(e)\in B\iff h(e)\notin B$ for all $e\in E$. For an edge $e$ let $\beta(e)$ be its black endpoint, and let $\delta_B(A)=\{e\in\delta(A):\beta(e)\in A\}$.
--
--   The *cap* $N^A$ of $A$ is the network obtained by contracting $V\setminus A$ to a single new vertex $\ast$ and discarding the edges with no endpoint in $A$: its vertex set is $A\cup\{\ast\}$, its edge set is $R(A)$, and an edge $e$ has tail $\pi(t(e))$ and head $\pi(h(e))$, where $\pi(v)=v$ for $v\in A$ and $\pi(v)=\ast$ for $v\notin A$. Color $N^A$ by keeping the colors of the vertices of $A$ and declaring
--   $$\ast\ \text{black}\iff\delta_B(A)=\varnothing ,$$
--   i.e. the new vertex is black exactly when no cut edge has its black endpoint inside $A$. Write $B^A$ for the resulting set of black vertices of $N^A$.
--
--   **Theorem.** Assume $N$ is simple (no loops, no two edges with the same endpoint pair), $G(N)$ is cubic (every vertex has exactly three neighbours), every edge of $N$ has exactly one black endpoint, and $A\subseteq V$ satisfies $|\delta(A)|=3$. Then every edge of the cap has exactly one black endpoint:
--
--   $$
--   \pi(t(e))\in B^A\iff\pi(h(e))\notin B^A\qquad\text{for every } e\in R(A).
--   $$
--
--   In other words, capping one side of a 3-edge cut of a simple cubic bipartite network yields a bipartite network whose coloring agrees with the original one on the kept side. This is what allows an argument for cubic bipartite graphs to be applied recursively to both sides of a nontrivial 3-edge cut.
--
--   **Formalization Note** The cap is `N.cap A : Network (Option A) (N.regionEdges A)`, with `none` playing the role of $\ast$, and the coloring is `N.capBlack black A`, where `none` is black iff `(N.blackCut black A).card = 0`. Black vertices are given by a predicate `black : V → Prop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean#L381-L411

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

theorem OAI.Barnette.Network.cap_coloring (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.cut A).card = 3) :
    ∀ e, N.capBlack black A ((N.cap A).tail e) ↔ ¬N.capBlack black A ((N.cap A).head e) := by sorry
