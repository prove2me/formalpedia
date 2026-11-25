-- Prove2me | Theorems.Thm_Kyprianou_Ch04_convolutionPowerPreservesProbability
-- name    : Kyprianou.Ch04.convolutionPowerPreservesProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:14:32.840176+00:00
-- url     : https://prove2.me/theorems/c4a652c2-602f-429a-bd00-42f5aa22b2af
-- title:
--   Probability is preserved by every finite convolution power
-- statement:
--   If eta is a probability measure on the real line, every finite convolution power starting at the Dirac mass at zero is again a probability measure. This is the convPow family in Kyprianou Theorem 4.10.
-- source:
--   Kyprianou (2006), Theorem 4.10, p. 100, geometric convolution stationary law; abstract step.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch04.convolutionPowerPreservesProbability
    (eta : Measure ℝ) [IsProbabilityMeasure eta] :
    ∀ n : ℕ, IsProbabilityMeasure
      (Nat.rec (Measure.dirac (0 : ℝ))
        (fun _ mu => mu.conv eta) n) := by
  sorry
