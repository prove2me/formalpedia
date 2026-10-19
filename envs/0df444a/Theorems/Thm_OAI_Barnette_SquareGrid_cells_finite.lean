-- Prove2me | Theorems.Thm_OAI_Barnette_SquareGrid_cells_finite
-- name    : OAI.Barnette.SquareGrid.cells_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:14:19.577238+00:00
-- url     : https://prove2.me/theorems/716d53f8-b85e-45f5-9a84-3c1e0976c5c5
-- title:
--   A compact planar set meets only finitely many square cells
-- statement:
--   For $\delta>0$ and $z=(z_1,z_2)\in\mathbb{Z}^2$, the closed square cell of side $\delta$ indexed by $z$ is
--   $$C_\delta(z)=[\delta z_1,\delta(z_1+1)]\times[\delta z_2,\delta(z_2+1)]\subseteq\mathbb{R}^2 .$$ For $K\subseteq\mathbb{R}^2$ let
--   $$\operatorname{cells}_\delta(K)=\{z\in\mathbb{Z}^2:\ C_\delta(z)\cap K\neq\varnothing\}$$
--   be the set of indices of cells meeting $K$.
--
--   **Theorem.** Let $\delta>0$ and let $K\subseteq\mathbb{R}^2$ be compact. Then
--
--   $$
--   \operatorname{cells}_\delta(K)\ \text{is a finite subset of}\ \mathbb{Z}^2 .
--   $$
--
--   Finiteness is what allows a compact piece of a plane drawing to be replaced by a finite set of lattice points, so that a plane graph can be modelled inside a finite part of the square grid.
--
--   **Formalization Note** The set of cells is `SquareGrid.cells δ K : Set (ℤ × ℤ)` and finiteness is `Set.Finite`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/SquareGrid.lean#L64-L77

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

theorem OAI.Barnette.SquareGrid.cells_finite {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) : (cells δ K).Finite := by sorry
