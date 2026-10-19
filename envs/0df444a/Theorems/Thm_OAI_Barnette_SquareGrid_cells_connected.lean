-- Prove2me | Theorems.Thm_OAI_Barnette_SquareGrid_cells_connected
-- name    : OAI.Barnette.SquareGrid.cells_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:15:22.001982+00:00
-- url     : https://prove2.me/theorems/71376fa7-f590-47d3-b2e7-69d2c394f505
-- title:
--   The square cells meeting a compact connected planar set induce a connected subgraph of the grid
-- statement:
--   For $\delta>0$ and $z=(z_1,z_2)\in\mathbb{Z}^2$, the closed square cell of side $\delta$ indexed by $z$ is
--   $$C_\delta(z)=[\delta z_1,\delta(z_1+1)]\times[\delta z_2,\delta(z_2+1)]\subseteq\mathbb{R}^2 .$$ Let $\operatorname{cells}_\delta(K)=\{z\in\mathbb{Z}^2: C_\delta(z)\cap K\neq\varnothing\}$. The *square grid graph* $\Gamma$ on $\mathbb{Z}^2$ joins $z$ and $z'$ when they agree in one coordinate and differ by exactly $1$ in the other. For $S\subseteq\mathbb{Z}^2$, $\Gamma[S]$ denotes the induced subgraph on $S$.
--
--   **Theorem.** Let $\delta>0$ and let $K\subseteq\mathbb{R}^2$ be compact and connected (in particular nonempty). Then
--
--   $$
--   \Gamma\bigl[\operatorname{cells}_\delta(K)\bigr]\ \text{is a connected graph}.
--   $$
--
--   Thus discretizing a compact connected set by the closed cells it meets produces a finite connected lattice region. Applied to the branches and edge cores of a plane drawing, it gives the connected vertex regions and corridors in the grid.
--
--   **Formalization Note** The grid graph is `SquareGrid.graph : SimpleGraph (ℤ × ℤ)`, the induced subgraph is `graph.induce (cells δ K)`, and connectedness is Mathlib's `SimpleGraph.Connected` (preconnected and nonempty).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/SquareGrid.lean#L169-L184

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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid

open OAI OAI.Barnette OAI.Barnette.SquareGrid

theorem OAI.Barnette.SquareGrid.cells_connected {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hc : IsConnected K) :
    (graph.induce (cells δ K)).Connected := by sorry
