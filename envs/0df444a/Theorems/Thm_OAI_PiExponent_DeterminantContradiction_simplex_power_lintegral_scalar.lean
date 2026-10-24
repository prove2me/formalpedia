-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral_scalar
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scalar
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:25:32.164291+00:00
-- url     : https://prove2.me/theorems/d99c8c7b-1b51-475c-9cc2-13864a7cd94e
-- title:
--   Scalar integral of the normalized simplex slice factor
-- statement:
--   The normalized power slice function integrates over `[0,T)` to `T/(m+1)`. Positivity of `T` supports the normalization and the power-integral evaluation; the formula includes `m = 0`.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scalar (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m)
      else 0) =
      ENNReal.ofReal (T / ((m + 1 : Nat) : Real)) := by sorry
