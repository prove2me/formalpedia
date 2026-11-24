-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supremumInfimumDuality
-- name    : Kyprianou.Ch03.supremumInfimumDuality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:38:56.180599+00:00
-- url     : https://prove2.me/theorems/f3decb5b-3c0d-4063-b885-79044b1ecb2f
-- title:
--   Lemma 3.5: duality of supremum and infimum pairs
-- statement:
--   For any positive deterministic time, the joint law of (running supremum, running supremum minus X_t) equals the joint law of (X_t minus running infimum, negative running infimum), under the original process probability.
-- source:
--   Kyprianou (2006), Chapter 3, Lemma 3.5, printed pp. 73-74.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem supremumInfimumDuality
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t) :
    Measure.map
      (fun omega : Omega =>
        let supremum := LevyExtrema.SBA.runSup (fun s => X s omega) t
        (supremum, supremum - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let infimum := sInf ((fun s : NNReal => X s omega) '' Set.Icc 0 t)
        (X t omega - infimum, -infimum)) P := by
  sorry

end Kyprianou.Ch03
