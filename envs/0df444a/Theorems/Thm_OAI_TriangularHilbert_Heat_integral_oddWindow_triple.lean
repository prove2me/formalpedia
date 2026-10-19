-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_integral_oddWindow_triple
-- name    : OAI.TriangularHilbert.Heat.integral_oddWindow_triple
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:00:34.400215+00:00
-- url     : https://prove2.me/theorems/6c5339df-aec9-4292-b0fd-e2789a4e65eb
-- title:
--   Triple convolution of odd Gaussian windows
-- statement:
--   The odd window is $\omega_s(t)=\frac{t}{\sqrt s}\phi_s(t)$ and the signed kernel is $\kappa_s(t)=\frac{t^3/27-ts/3}{s\sqrt s}\phi_{3s}(t)$, with $\phi_\sigma$ the centred Gaussian density of variance $\sigma$. For $s>0$ and $a,b,c\in\mathbb R$,
--   $$
--   \int_{\mathbb R^2}\omega_s(a-z_1)\,\omega_s(b-z_2)\,\omega_s(c+z_1+z_2)\,dz=\kappa_s(a+b+c).
--   $$
--
--   Integrating the three odd windows over the plane of centres produces the signed cubic kernel evaluated at the cyclic sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SignedConvolution.lean#L75-L93

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory

theorem OAI.TriangularHilbert.Heat.integral_oddWindow_triple {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    (∫ z : ℝ×ℝ, oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) =
      signedKernel s (a+b+c) := by sorry
