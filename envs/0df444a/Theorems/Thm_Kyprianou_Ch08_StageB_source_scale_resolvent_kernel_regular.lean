-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_kernel_regular
-- name    : Kyprianou.Ch08.StageB.source_scale_resolvent_kernel_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:45:05.573184+00:00
-- url     : https://prove2.me/theorems/4c178329-be79-489c-bc00-aeec209692cd
-- title:
--   Source zero-discount Volterra resolvent regularity on x>0
-- statement:
--   For any source scale family Wq and q≥0, the positive-x Volterra expression W0(x)+q(W0∗Wq)(x) is continuous on (0,∞) and nonnegative there. Apply source W0 continuity/positivity and existing Proved Avram positive_causal_convolution_continuous_of_weighted_integrable with a weight β>Φψ(q), using the exact IsQScale source transform. This supplies the regularity assumptions of the Proved Laplace uniqueness theorem in Lemma 8.3.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3, (8.24), printed p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- Source q-scale Volterra expression is nonnegative and continuous for x>0. -/
theorem source_scale_resolvent_kernel_regular
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ContinuousOn (fun x : ℝ => W 0 x + q *
        (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume)) (Set.Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x → 0 ≤ (fun x : ℝ => W 0 x + q *
        (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume)) x) := by
  sorry

end Kyprianou.Ch08.StageB
