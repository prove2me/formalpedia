-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_finite_mesh_energy_jump_le
-- name    : OAI.TriangularHilbert.Heat.finite_mesh_energy_jump_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:15:25.050254+00:00
-- url     : https://prove2.me/theorems/6e39d2e1-b2cc-4104-898d-d6911a66d655
-- title:
--   Energy jumps on a grid are controlled by maximal slicing weights
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The total plane energy $\sum_v\mathrm{planeIntegral}\bigl(\mathrm{heatEnergy}(\cdot,v),d\bigr)$ adds the $S^3$-energies $\operatorname{tr}(R_v^*R_v)^{3/2}$ of the three heat-weighted star rows, integrated over the centres. On a grid $D\subset\mathbb Z$ with positions $u_m=hm$ and variances $\sigma_v\ge h^2$, let $B,C$ be entrywise dominated by $A_0$. Then
--   $$
--   \Bigl|\mathrm{TPE}\bigl(\mathrm{replaceZero}(A,B)\bigr)-\mathrm{TPE}\bigl(\mathrm{replaceZero}(A,C)\bigr)\Bigr|\le\frac32\,C_{\mathrm{mesh}}\,h^2\sum_{i,j}|B_{ij}-C_{ij}|\,\mathrm{jumpMax}(i,j),
--   $$
--   with $C_{\mathrm{mesh}}=2e^{1/2}$ and $\mathrm{jumpMax}$ the maximal slicing weight.
--
--   The jump bound becomes uniform in the variances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MeshJump.lean#L52-L71

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators

theorem OAI.TriangularHilbert.Heat.finite_mesh_energy_jump_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (B C : Matrix D D ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) :
    |totalPlaneEnergy (replaceZero A B) h (fun m => h*(m:ℤ)) 0 σ-
      totalPlaneEnergy (replaceZero A C) h (fun m => h*(m:ℤ)) 0 σ| ≤
      3/2*meshMassConstant*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpMax D A i j := by sorry
