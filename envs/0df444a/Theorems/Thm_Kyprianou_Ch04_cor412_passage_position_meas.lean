-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_passage_position_meas
-- name    : Kyprianou.Ch04.cor412_passage_position_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:39:18.864713+00:00
-- url     : https://prove2.me/theorems/bc5f9a36-dc08-466f-862f-56259de689f5
-- title:
--   Passage position measurable under restricted measure
-- statement:
--   Passage position measurable under restricted measure.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12, supporting lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_passage_meas
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The arbitrary finite-time representative gives a measurable passage position under the restricted measure. -/

theorem Kyprianou.Ch04.cor412_passage_position_meas {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    AEMeasurable (fun w => L.X (finiteTime w) w)
      (P.restrict {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}) := by sorry
