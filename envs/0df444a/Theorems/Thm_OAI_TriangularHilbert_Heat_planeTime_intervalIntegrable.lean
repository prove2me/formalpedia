-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_planeTime_intervalIntegrable
-- name    : OAI.TriangularHilbert.Heat.planeTime_intervalIntegrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:19:01.461316+00:00
-- url     : https://prove2.me/theorems/1861d8d3-2168-45c7-823a-f28416d72dd1
-- title:
--   Time integrability of plane-integrated variance and cost terms
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. Let $h>0$, rates $\alpha_w>0$ and $0<a\le b$. With variances $\sigma_w=\alpha_wt$, the functions
--   $$
--   t\longmapsto\mathrm{planeIntegral}\bigl(\mathrm{heatVariance}(\cdot,v,w)\bigr),\qquad t\longmapsto\mathrm{planeIntegral}\bigl(\mathrm{heatCost}(\cdot,v,w)\bigr)
--   $$
--   are interval integrable on $[a,b]$ for all vertices $v,w$.
--
--   So the energy identity of the heat flow can be integrated in time.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneInterval.lean#L24-L68

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
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.planeTime_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∀ v w, IntervalIntegrable (fun t => planeIntegral (fun p => heatVariance A h u p (fun z => α z*t) v w) d) volume a b) ∧
    (∀ v w, IntervalIntegrable (fun t => planeIntegral (fun p => heatCost A h u p (fun z => α z*t) v w) d) volume a b) := by sorry
