-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_sq_sum_of_condExp_eq_zero
-- name    : LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:27:11.868548+00:00
-- url     : https://prove2.me/theorems/69572ad0-b836-46e5-88e3-64e54bfffb37
-- title:
--   integral sq sum of condExp eq zero
-- statement:
--   The source theorem `LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero` is extracted from `LevyStochCalc.Probability.MartingaleDifference`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_MartingaleDifference_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of martingale differences

A finite family `Y 0, …, Y (n-1)` in `L²` with `Y k` measurable for `𝒢 (k+1)` and
`𝔼[Y k | 𝒢 k] = 0` is orthogonal, so the second moment of the sum is the sum of the second
moments.

## Main statements

* `LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero` — a partial sum is orthogonal
  to the next difference.
* `LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero` — the second moment of a sum of
  martingale differences is the sum of the second moments.
-/

namespace LevyStochCalc.Probability

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

section MartingaleDifference

variable (𝒢 : ℕ → MeasurableSpace Ω) (h𝒢le : ∀ k, 𝒢 k ≤ mΩ) (h𝒢mono : Monotone 𝒢)
  (Y : ℕ → Ω → ℝ) (hY : ∀ k, MemLp (Y k) 2 P)
  (hYmeas : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (Y k))
  (hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0)

include h𝒢le h𝒢mono hY hYmeas hYcond in

theorem _root_.LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      = ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P := by sorry
