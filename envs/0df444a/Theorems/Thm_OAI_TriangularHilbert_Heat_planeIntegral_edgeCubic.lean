-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_planeIntegral_edgeCubic
-- name    : OAI.TriangularHilbert.Heat.planeIntegral_edgeCubic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:56:19.56637+00:00
-- url     : https://prove2.me/theorems/454d54b8-1577-440f-8f93-be87ca55b288
-- title:
--   Plane integral of the heat-weighted cubic edge mass
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For positive variances, the heat-weighted cubic mass of edge $v$ is $\sum_{i,j}|A_v(i,j)|^3g_v(i)g_{v+1}(j)$ with heat weights $g_w(i)=h\phi_{\sigma_w}(u_i-p_w)$. Integrated over the centres with $p_0+p_1+p_2=d$,
--   $$
--   \mathrm{planeIntegral}\bigl(\mathrm{edgeCubic}(\cdot,v),d\bigr)=\sum_{i,j}h^2\,|A_v(i,j)|^3 .
--   $$
--
--   Averaging over centres removes the heat weights exactly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MassPlane.lean#L68-L81

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type uι} [Fintype ι]

theorem OAI.TriangularHilbert.Heat.planeIntegral_edgeCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => edgeCubic A h u p σ v) d = ∑ i, ∑ j, h^2 * ‖A v i j‖^3 := by sorry
