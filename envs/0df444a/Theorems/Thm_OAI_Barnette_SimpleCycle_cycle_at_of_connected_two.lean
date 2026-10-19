-- Prove2me | Theorems.Thm_OAI_Barnette_SimpleCycle_cycle_at_of_connected_two
-- name    : OAI.Barnette.SimpleCycle.cycle_at_of_connected_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:06:33.474835+00:00
-- url     : https://prove2.me/theorems/73724503-09db-4c2d-9fea-31aac7e60cf6
-- title:
--   A connected 2-regular finite graph has a Hamiltonian cycle through any prescribed vertex
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$. It is *2-regular* if every vertex has exactly two neighbours. A *Hamiltonian cycle based at $v$* is a closed walk $v=x_0,x_1,\dots,x_n=v$ in $G$ (consecutive vertices adjacent) that is a cycle, meaning $n\ge 3$, no edge is used twice and $x_1,\dots,x_n$ are pairwise distinct, and that visits every vertex: each vertex of $V$ occurs exactly once among $x_1,\dots,x_n$.
--
--   **Theorem.** If $G$ is connected and 2-regular, then for every vertex $v\in V$ there is a closed walk $p$ from $v$ to $v$ that is a Hamiltonian cycle:
--
--   $$
--   \forall v\in V\ \ \exists\,p=(v=x_0,x_1,\dots,x_n=v):\quad p\ \text{is a cycle and}\ V=\{x_1,\dots,x_n\}\ \text{with the } x_i \text{ distinct}.
--   $$
--
--   This is the familiar fact that a finite connected graph in which every vertex has degree two is a single cycle, stated so that the base point of the cycle can be prescribed. It converts a connected spanning 2-regular subgraph into a Hamiltonian cycle of the ambient graph, which is the form of conclusion required for cubic bipartite planar graphs.
--
--   **Formalization Note** The cycle is a Mathlib walk `p : G.Walk v v` with `p.IsHamiltonianCycle`, i.e. `p.IsCycle` together with each vertex occurring exactly once in the support of `p.tail`. Regularity is `G.IsRegularOfDegree 2`, with degrees computed from classical finiteness of neighbour sets; equality on $V$ is assumed decidable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean#L187-L210

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

open OAI OAI.Barnette
open scoped Classical
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem OAI.Barnette.SimpleCycle.cycle_at_of_connected_two [DecidableEq V] (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by sorry
