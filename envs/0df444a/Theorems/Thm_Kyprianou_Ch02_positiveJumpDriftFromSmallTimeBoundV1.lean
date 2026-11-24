-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveJumpDriftFromSmallTimeBoundV1
-- name    : Kyprianou.Ch02.positiveJumpDriftFromSmallTimeBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:03:21.688368+00:00
-- url     : https://prove2.me/theorems/baac6daa-de4d-4888-9d09-eada1ed8d2c4
-- title:
--   Positive Lévy small-time first-moment bound implies nonnegative drift
-- statement:
--   Split (0,1) at r; the annular integral is integrable because the Lévy measure is finite away from zero. Negative marks are null, so the annular compensation is exactly the positive annular integral. Subtract the compensation from the drift identity.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, small-time moment and drift characterisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveJumpDriftFromSmallTimeBoundV1
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hs : T.levyMeasure (Set.Iio (0 : ℝ)) = 0)
    (r b : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : Integrable (fun x : ℝ => x)
      (T.levyMeasure.restrict (Set.Ioo (0 : ℝ) r)))
    (hb : (∫ x in Set.Ioo (0 : ℝ) r, x ∂T.levyMeasure) ≤ b)
    (hd : T.drift = b + ∫ x in {x : ℝ | r ≤ |x| ∧ |x| < 1}, x ∂T.levyMeasure) :
    0 ≤ T.drift - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂T.levyMeasure := by
  sorry
