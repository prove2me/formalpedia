-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_weight_three_integrable
-- name    : OAI.TriangularHilbert.Heat.weight_three_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:04:13.285893+00:00
-- url     : https://prove2.me/theorems/b454aa61-0857-4c81-abc4-ed1e5bfaaa35
-- title:
--   Integrability of three heat weights over the plane of centres
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$. Let $h>0$ and $\sigma_w>0$. Parametrize the centres by $p=(z_1,z_2,d-z_1-z_2)$. For positions $a,b,c$ and a vertex $v$, the function
--   $$
--   z\longmapsto h\phi_{\sigma_0}(a-p_0)\cdot h\phi_{\sigma_1}(b-p_1)\cdot h\phi_{\sigma_v}(c-p_v)
--   $$
--   is integrable on $\mathbb R^2$.
--
--   Products of heat weights at the vertices are integrable over the plane of centres.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GaussianExpectation.lean#L10-L28

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory

theorem OAI.TriangularHilbert.Heat.weight_three_integrable {h : ℝ} (hh : 0 < h) (a b c d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h c (chart 2 d z v) (σ v)) := by sorry
