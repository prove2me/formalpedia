-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_integrated_strict_dissipation
-- name    : OAI.TriangularHilbert.Heat.integrated_strict_dissipation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:20:09.227742+00:00
-- url     : https://prove2.me/theorems/ebb1d913-57e5-4774-99b4-810a74586308
-- title:
--   Integrated strict energy dissipation of the heat flow
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The total plane energy $\mathrm{TPE}(\sigma)$ is the sum over the three vertices of the heat star energies $\operatorname{tr}(R_v^*R_v)^{3/2}$, integrated over centres $p_0+p_1+p_2=d$. Under strict rates the variances are $\sigma_w=s$ at a distinguished vertex $r$ and $\frac{11}{10}s$ at the other two, and $c_\ast=\frac12\min\bigl(1-\frac35\sqrt2,\frac{11}{10}-\frac12\sqrt2\bigr)$. Let $h>0$ and $0<a\le b$. Then
--   $$
--   c_\ast\int_a^b\sum_w\mathrm{planeIntegral}\bigl(\mathrm{heatCost}(\cdot,w,w)\bigr)\big|_{\sigma=\mathrm{strict}(s)}\,ds\le\mathrm{TPE}\bigl(\mathrm{strict}(a)\bigr)-\mathrm{TPE}\bigl(\mathrm{strict}(b)\bigr).
--   $$
--
--   Along the heat flow the matrix energy decreases at a rate at least $c_\ast$ times the Hessian costs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/IntegratedDissipation.lean#L39-L56

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.integrated_strict_dissipation (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (i : Three)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    strictConstant * (∫ s in a..b, ∑ w, planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) ≤
      totalPlaneEnergy A h u d (fun w => strictRate i w*a) - totalPlaneEnergy A h u d (fun w => strictRate i w*b) := by sorry
