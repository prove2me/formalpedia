-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_resolvent_weighted_integrable
-- name    : Kyprianou.Ch08.StageB.source_resolvent_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:48:47.735311+00:00
-- url     : https://prove2.me/theorems/411168b6-9fc7-43de-9a7d-aa6777bab1c1
-- title:
--   Weighted integrability of the genuine q-scale Volterra expression
-- statement:
--   For β above both source scale roots, the weighted real function exp(-βx)[W0(x)+q(W0∗Wq)(x)] is integrable over x>0. Source IsQScale gives weighted integrability of W0; Proved Avram positive_causal_convolution_laplace_integrable gives integrability of the convolution; linearity and scalar multiplication prove the conclusion. This directly discharges the second integrability hypothesis of the Proved Laplace uniqueness theorem for the source resolvent.
-- source:
--   Kyprianou (2006), Lemma 8.3 (8.24), p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- Weighted integrability of the source q-scale Volterra resolvent expression. -/
theorem source_resolvent_weighted_integrable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q θ : ℝ)
    (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
      (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume)))
      (Set.Ioi (0 : ℝ)) volume := by
  sorry

end Kyprianou.Ch08.StageB
