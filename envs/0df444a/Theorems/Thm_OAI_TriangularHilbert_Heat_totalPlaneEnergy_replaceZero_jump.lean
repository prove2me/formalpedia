-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_totalPlaneEnergy_replaceZero_jump
-- name    : OAI.TriangularHilbert.Heat.totalPlaneEnergy_replaceZero_jump
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:09:16.911828+00:00
-- url     : https://prove2.me/theorems/41ed1f05-6725-4818-b9ff-d50374b6e163
-- title:
--   Jump of the total plane energy when edge zero is changed
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The total plane energy $\sum_v\mathrm{planeIntegral}\bigl(\mathrm{heatEnergy}(\cdot,v),d\bigr)$ adds the $S^3$-energies $\operatorname{tr}(R_v^*R_v)^{3/2}$ of the three heat-weighted star rows, integrated over the centres. Let $B,C$ be entrywise dominated by $A_0$, $h>0$ and $\sigma_v>0$. Then, with centre sum $0$,
--   $$
--   \Bigl|\mathrm{TPE}\bigl(\mathrm{replaceZero}(A,B)\bigr)-\mathrm{TPE}\bigl(\mathrm{replaceZero}(A,C)\bigr)\Bigr|\le\frac32h^2\sum_{i,j}|B_{ij}-C_{ij}|\,J(i,j),
--   $$
--   where $J(i,j)$ is the jump expectation: the slicing weight of the entry $(i,j)$ with Gaussian convolutions of the variances.
--
--   Switching an entry changes the averaged energy in proportion to its slices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/TotalJump.lean#L108-L139

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.totalPlaneEnergy_replaceZero_jump (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) :
    |totalPlaneEnergy (replaceZero A B) h u 0 σ-totalPlaneEnergy (replaceZero A C) h u 0 σ| ≤
      3/2*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpExpectation A h u σ i j := by sorry
