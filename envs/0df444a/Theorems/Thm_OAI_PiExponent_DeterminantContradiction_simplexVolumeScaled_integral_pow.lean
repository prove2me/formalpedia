-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_integral_pow
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_integral_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:46:59.934737+00:00
-- url     : https://prove2.me/theorems/ad7dc091-970b-4c5c-8823-4da25b3328dc
-- title:
--   Integral formula for the simplex power slices
-- statement:
--   The ENNReal integral over [0,r] of the n-th power of the remaining scale, divided by n!, equals the ENNReal coercion of r^(n+1)/(n+1)!.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_integral_pow (n : Nat) (r : Real) (hr : 0 ≤ r) :
    (∫⁻ t in Set.Icc (0 : Real) r,
      ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real)) ∂MeasureTheory.volume) =
        ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by sorry
