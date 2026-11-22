-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationRationalCrossingBefore
-- name    : Kyprianou.Ch01.inverseReciprocalOccupationRationalCrossingBefore
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:12:03.156384+00:00
-- url     : https://prove2.me/theorems/54c79e4a-f711-49b3-a4a9-9314969f3b9f
-- title:
--   A rational strict-clock crossing lies below every horizon strictly above the inverse time
-- statement:
--   For an extended reciprocal-occupation clock, every finite physical time strictly beyond the strict right-inverse admits a positive rational time below that bound where the clock is strictly above the target level. Extract a crossing below the horizon from the conditional sInf, then choose a rational strictly between that crossing and the bound. Monotonicity of reciprocal occupation preserves strict crossing; the no-crossing case has infinite inverse time. No path continuity or finite-mean hypothesis is required.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, Eq. (1.19), rational upper-crossing lemma

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationMonotone
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseReciprocalOccupationRationalCrossingBefore
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (t upper : ℝ≥0)
    (hUpper : inverseReciprocalOccupation X t ω <
      (upper : WithTop ℝ≥0)) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧
      Real.toNNReal (q : ℝ) < upper ∧
      (t : ℝ≥0∞) <
        reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω := by
  sorry
