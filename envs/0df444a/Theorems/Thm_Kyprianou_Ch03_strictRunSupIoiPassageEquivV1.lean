-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strictRunSupIoiPassageEquivV1
-- name    : Kyprianou.Ch03.strictRunSupIoiPassageEquivV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:11:53.799373+00:00
-- url     : https://prove2.me/theorems/e8e69b25-8883-4e88-9914-fb38b177f01a
-- title:
--   Strict running supremum and strictly earlier first upward passage
-- statement:
--   For positive barriers of a spectrally negative Levy process started at zero, a strict running supremum exceedance up to t is equivalent to strict first passage before t. Use compact boundedness, the infimum definition of passage, and the proved no-positive-jump first-upcrossing value identity.
-- source:
--   Kyprianou (2006) Chapter 3 Exercise 3.6; parent 8f6cb341-363a-4934-8bb1-c48730f77e03.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strictRunSupIoiPassageEquivV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (hx : 0 < x) (omega : Omega) (t : NNReal) :
    x < LevyExtrema.SBA.runSup (fun s => L.X s omega) t ↔
      Kyprianou.Ch03.firstHittingTime L.X (Set.Ioi x) omega <
        (t : WithTop NNReal) := by sorry
