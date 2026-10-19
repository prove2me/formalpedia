-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_totalPlaneEnergy_le_mass
-- name    : OAI.TriangularHilbert.Heat.totalPlaneEnergy_le_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:08:33.551127+00:00
-- url     : https://prove2.me/theorems/e76a5966-1042-41bc-88a5-ad132dc8b714
-- title:
--   The total plane energy is bounded by the cubic mass of the array
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The total plane energy $\sum_v\mathrm{planeIntegral}\bigl(\mathrm{heatEnergy}(\cdot,v),d\bigr)$ adds the $S^3$-energies $\operatorname{tr}(R_v^*R_v)^{3/2}$ of the three heat-weighted star rows, integrated over the centres. Let $h>0$, $\sigma_v>0$, and suppose that the heat weights satisfy $\sum_ih\phi_{\sigma_v}(u_i-p_v)\le M$ for all centres and vertices. Then
--   $$
--   \sum_v\mathrm{planeIntegral}\bigl(\mathrm{heatEnergy}(\cdot,v),d\bigr)\le2\sqrt2\,M\sum_v\sum_{i,j}h^2|A_v(i,j)|^3 .
--   $$
--
--   The heat-flow energy is controlled by the discrete $L^3$ masses of the three functions at all times.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/InitialPlane.lean#L27-L55

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.totalPlaneEnergy_le_mass (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v)
    {M : ℝ} (hM : 0 ≤ M) (hm : ∀ p v, (∑ i, heatWeights h u p σ v i) ≤ M) :
    totalPlaneEnergy A h u d σ ≤ 2*Real.sqrt 2*M*arrayCubic A h := by sorry
