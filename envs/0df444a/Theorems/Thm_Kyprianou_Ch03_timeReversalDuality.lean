-- Prove2me | Theorems.Thm_Kyprianou_Ch03_timeReversalDuality
-- name    : Kyprianou.Ch03.timeReversalDuality
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:38:29.737296+00:00
-- url     : https://prove2.me/theorems/738b23d9-7a4a-4950-8e30-28b1734d73dd
-- title:
--   Lemma 3.4: time-reversal duality with left limits
-- statement:
--   For a fixed strictly positive horizon, the entire reversed Levy path indexed by 0<=s<=t, using the left limit at t-s (and the original starting value at s=t), has the same law as the reflected original path -X_s. This preserves the jump-sensitive reversal.
-- source:
--   Kyprianou (2006), Chapter 3, Lemma 3.4, printed pp. 73-74.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem timeReversalDuality
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t) :
    Measure.map
      (fun omega : Omega =>
        fun s : {s : NNReal // s <= t} =>
          (if (s : NNReal) = t then X 0 omega
           else Function.leftLim (fun r : NNReal => X r omega) (t - (s : NNReal))) -
             X t omega) P =
    Measure.map
      (fun omega : Omega =>
        fun s : {s : NNReal // s <= t} =>
          -(X (s : NNReal) omega)) P := by
  sorry

end Kyprianou.Ch03
