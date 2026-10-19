-- Prove2me | Theorems.Thm_OAI_Barnette_SimpleCycle_delete_vertex_connected
-- name    : OAI.Barnette.SimpleCycle.delete_vertex_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:07:08.821567+00:00
-- url     : https://prove2.me/theorems/0b0a6f93-1402-463f-a755-c3dde6b856f7
-- title:
--   Deleting one vertex from a connected 2-regular finite graph leaves a connected graph
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ that is connected and *2-regular* (every vertex has exactly two neighbours). For $S\subseteq V$ write $G[S]$ for the subgraph induced on $S$: its vertices are the elements of $S$ and two of them are adjacent iff they are adjacent in $G$.
--
--   **Theorem.** For every vertex $v\in V$, the graph obtained by deleting $v$ is connected:
--
--   $$
--   G\bigl[V\setminus\{v\}\bigr]\ \text{is connected}\qquad\text{for every } v\in V .
--   $$
--
--   Here connectedness includes nonemptiness; it holds because a connected 2-regular finite graph is a single cycle with at least three vertices, and removing a vertex from a cycle leaves a path. The lemma is used for a connected 2-regular spanning subgraph of a capped graph (that is, a Hamiltonian cycle of it) passing through the contracted vertex: deleting that vertex leaves a connected graph on the kept side, and this connectivity is transported back to the original network.
--
--   **Formalization Note** The deleted graph is `G.induce {w | w ≠ v}`; regularity is `G.IsRegularOfDegree 2` with classical decidability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean#L223-L247

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

theorem OAI.Barnette.SimpleCycle.delete_vertex_connected (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    (G.induce {w | w ≠ v}).Connected := by sorry
