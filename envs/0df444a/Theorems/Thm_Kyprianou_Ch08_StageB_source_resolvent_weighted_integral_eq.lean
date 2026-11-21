-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_resolvent_weighted_integral_eq
-- name    : Kyprianou.Ch08.StageB.source_resolvent_weighted_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:48:47.008929+00:00
-- url     : https://prove2.me/theorems/1fe342fb-3472-4944-9842-1c52fdae2e3f
-- title:
--   Source discounted scale equals Volterra expression after weighted integration
-- statement:
--   For β above both source roots, the Laplace transform of actual Wq is exactly the Laplace transform of W0+q(W0∗Wq). Apply source IsQScale transform for Wq and the separately Proved source_scale_resolvent_laplace_scalar, then use integrability and integral linearity to identify the two transforms. This is the exact identity premise in the Proved nonnegative continuous Laplace uniqueness theorem.
-- source:
--   Kyprianou (2006), Lemma 8.3 (8.24), p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- Genuine q-scale and Volterra expression have equal weighted Laplace transforms. -/
theorem source_resolvent_weighted_integral_eq
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q θ : ℝ)
    (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) * W q x ∂volume) =
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) *
      (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume)) ∂volume) := by
  sorry

end Kyprianou.Ch08.StageB
