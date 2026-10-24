-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_interval_support_interval_integral_of_support
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.interval_integral_of_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:34:45.962156+00:00
-- url     : https://prove2.me/theorems/158335a9-4ab2-4560-ae6f-41439f8830cc
-- title:
--   Restrict an integral to an interval from support and interior agreement
-- statement:
--   For a positive endpoint, if a real-valued function vanishes strictly outside the interval and agrees with another function in its interior, then its full integral equals the other function's interval integral; endpoint values are immaterial.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.interval_integral_of_support {H : Real} (hH : 0 < H) (f g : Real → Real) (hout : ∀ t, t < 0 ∨ H < t → f t = 0) (hmid : ∀ t, 0 < t → t < H → f t = g t) :
    (∫ t : Real, f t) = ∫ t in (0 : Real)..H, g t := by sorry
