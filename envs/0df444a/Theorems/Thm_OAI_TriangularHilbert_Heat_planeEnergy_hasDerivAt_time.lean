-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_planeEnergy_hasDerivAt_time
-- name    : OAI.TriangularHilbert.Heat.planeEnergy_hasDerivAt_time
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:53:47.526174+00:00
-- url     : https://prove2.me/theorems/ab966ba5-a13a-47fd-ae92-24e7d4d5340c
-- title:
--   Time derivative of the plane-integrated heat energy
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For a triangle array $A$, mesh $h>0$, positions $u$, centres $p=(p_0,p_1,p_2)$ and variances $\sigma$, the heat star energies $\mathrm{heatEnergy}(v)$, their centre and variance derivatives ($\mathrm{heatFirst}$, $\mathrm{heatPure}$, $\mathrm{heatVariance}$), the Hessian costs $\mathrm{heatCost}(v,w)$ and the mixed Hessian terms $\mathrm{heatMixed}(v,w,z)$ are real numbers attached to each vertex. Centres with $p_0+p_1+p_2=d$ are parametrized by $\mathrm{chart}(i,d,z)$, $z\in\mathbb R^2$, and $\mathrm{planeIntegral}(f,d)=\int_{\mathbb R^2}f(\mathrm{chart}(2,d,z))\,dz$. Let $h>0$, rates $\alpha_w>0$, $s>0$, and let the variances grow linearly in time, $\sigma_w=\alpha_wt$. Then for every vertex $v$,
--   $$
--   \frac{d}{dt}\Big|_{t=s}\mathrm{planeIntegral}\bigl(\mathrm{heatEnergy}(\cdot,v)\bigr)=\sum_w\alpha_w\,\mathrm{planeIntegral}\bigl(\mathrm{heatVariance}(\cdot,v,w)\bigr)\Big|_{\sigma=\alpha s} .
--   $$
--
--   The energy integrated over centres evolves by the chain rule through the three variances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneTime.lean#L14-L66

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.Heat.planeEnergy_hasDerivAt_time (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) (v : Three) :
    HasDerivAt (fun t => planeIntegral (fun p => heatEnergy A h u p (fun w => α w*t) v) d)
      (∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d) s := by sorry
