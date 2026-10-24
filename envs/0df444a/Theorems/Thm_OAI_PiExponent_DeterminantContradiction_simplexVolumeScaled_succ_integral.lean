-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:38:24.46628+00:00
-- url     : https://prove2.me/theorems/cad44eee-a00a-49c7-8fa9-a9d5d4c95100
-- title:
--   Evaluate the sliced simplex integral from the lower-dimensional formula
-- statement:
--   Use the lower-dimensional formula at each residual scale r − t and evaluate its integral over 0 ≤ t ≤ r. The proof route is the real power integral together with (n+1)! = (n+1)n!; the endpoints also satisfy the stated formula, including r = 0.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral
    (n : Nat) (r : Real) (hr : 0 ≤ r)
    (ih : ∀ s : Real, 0 ≤ s →
      MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ s} =
        ENNReal.ofReal (s ^ n / (Nat.factorial n : Real))) :
    (∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume) =
      ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by sorry
