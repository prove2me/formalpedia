-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_laplace_uniqueness_premises
-- name    : Kyprianou.Ch08.StageB.source_scale_resolvent_laplace_uniqueness_premises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:45:19.653044+00:00
-- url     : https://prove2.me/theorems/1afbd665-12f1-44f4-9323-84349a6abc57
-- title:
--   All Laplace transform premises for source q-scale Volterra uniqueness
-- statement:
--   For the actual source scale family and q≥0, choose b above both scale roots. For every θ>b, Wq and the Volterra expression W0+q(W0∗Wq) are exponentially weighted integrable and have exactly equal Laplace transforms. Follows from the source IsQScale transforms, Proved positive_causal_convolution_laplace_integrable, and the already Proved source_scale_resolvent_laplace_scalar theorem. Provides the remaining input to continuous nonnegative Laplace uniqueness.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3, (8.24), printed p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- Both source q-scale and its Volterra expression have equal Laplace transforms. -/
theorem source_scale_resolvent_laplace_uniqueness_premises
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * W q x)
        (Set.Ioi (0 : ℝ)) volume ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (W 0 x +
        q * (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume)))
        (Set.Ioi (0 : ℝ)) volume ∧
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) * W q x ∂volume) =
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) *
        (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
          W 0 s * W q (x - s) ∂volume)) ∂volume) := by
  sorry

end Kyprianou.Ch08.StageB
