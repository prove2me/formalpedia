-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationRationalInf
-- name    : Kyprianou.Ch01.inverseReciprocalOccupationRationalInf
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:07:45.535256+00:00
-- url     : https://prove2.me/theorems/c2721aeb-d844-4530-b9c1-9e113185dfe4
-- title:
--   Strict reciprocal-occupation inverse equals its countable rational upper-crossing infimum
-- statement:
--   For each integer-valued physical path and branching clock level, the extended strict right-inverse of its monotone ENNReal reciprocal-occupation clock equals the infimum of all strictly positive rational physical times at which the clock exceeds the level, with top for absent crossings. Rational times approach a crossing time from above, and monotonicity preserves strict crossing; no continuous-path, finite-moment or finite-clock hypothesis is used.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, equation (1.19), countable monotone-clock rational reduction

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationMonotone
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseReciprocalOccupationRationalInf
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (t : ℝ≥0) :
    inverseReciprocalOccupation X t ω =
      ⨅ q : ℚ,
        if (0 < (q : ℝ) ∧
            (t : ℝ≥0∞) <
              reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω)
          then ((Real.toNNReal (q : ℝ)) : WithTop ℝ≥0)
          else ⊤ := by
  sorry
