-- Prove2me | Theorems.Thm_Kyprianou_Ch06_inverseLocalTimeStoppingTimes
-- name    : Kyprianou.Ch06.inverseLocalTimeStoppingTimes
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:03:18.204369+00:00
-- url     : https://prove2.me/theorems/a8aa4984-be4b-4ec6-8184-52fd26acda98
-- title:
--   Lemma 6.9: inverse local time and its left limit are stopping times
-- statement:
--   Let X be a Lévy process and L its adapted right-continuous local time at the running supremum in either the continuous or exponential-jump clock regime, under the usual right-continuous filtration. Then for every nonnegative level s the first chronological passage time at which L exceeds s and the left limit of that inverse at s are stopping times. This is the entire conclusion of Lemma 6.9.
-- source:
--   Kyprianou (2006), first edition, Lemma 6.9, printed p. 148; physical two-up PDF p. 79.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
open MeasureTheory Filter
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Lemma 6.9: each inverse-local-time level and its left limit are
stopping times for the right-continuous filtration of the original process.
Both regular and irregular local-time clocks are included. -/
theorem inverseLocalTimeStoppingTimes
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L) :
  ∀ s : NNReal,
    IsStopTime F (fun omega => inverseLocalTime L s omega) ∧
    IsStopTime F (fun omega => inverseLocalTimeLeft L s omega) := by
  sorry

end Kyprianou.Ch06
