-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_power_real_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_real_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:59:08.117881+00:00
-- url     : https://prove2.me/theorems/68ca6a3c-ad9e-4d76-aed0-fb34765a1748
-- title:
--   Evaluate the real residual-power integral
-- statement:
--   For natural `n` and `0 <= r`, the real integral of `(r - t)^n / n!` over `[0,r]` equals `r^(n+1)/(n+1)!`, including `n = 0` and `r = 0`.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_real_integral (n : Nat) (r : Real) (hr : 0 <= r) : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) r)) (fun t : Real => (r - t) ^ n / (Nat.factorial n : Real)) = r ^ (n + 1) / (Nat.factorial (n + 1) : Real) := by sorry
