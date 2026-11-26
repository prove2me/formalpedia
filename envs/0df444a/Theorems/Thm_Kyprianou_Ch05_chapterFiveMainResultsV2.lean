-- Prove2me | Theorems.Thm_Kyprianou_Ch05_chapterFiveMainResultsV2
-- name    : Kyprianou.Ch05.chapterFiveMainResultsV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:32:04.133741+00:00
-- url     : https://prove2.me/theorems/e1360d93-f7f4-49fb-902c-7179bbaaa14a
-- title:
--   Chapter 5 cumulative goal: all sixteen numbered results and nine exercises (corrected)
-- statement:
--   Complete chapter certificate preserving every original numbered result and exercise, with Borel measurability added to the key renewal theorem.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, printed pp. 111-138 and nine exercises on pp. 133-138.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupA
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupB
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupC
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupD
import Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupE
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
/-- Complete chapter certificate requiring every numbered result and exercise. -/
theorem chapterFiveMainResultsV2 :
    (∀ (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F),
    let mu := ∫ x : Real, x ∂F;
        let V := renewalMeasure F;
        ((NonLatticeMeasure F →
          ∀ y : Real, 0 < y →
            Tendsto
              (fun x : Real => (V (Set.Ioc x (x + y))).toReal)
              atTop (nhds (y / mu))) ∧
         (NonLatticeMeasure F →
          ∀ h : Real → Real, Measurable h → DirectlyRiemannIntegrable h →
            Tendsto
              (fun x : Real =>
                ∫ z in Set.Icc (0 : Real) x, h (x - z) ∂V)
              atTop
              (nhds ((∫ z in Set.Ici (0 : Real), h z ∂volume) / mu))) ∧
         (Tendsto
           (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
           atTop (nhds (1 / mu))))) ∧
    certificate_5_2 ∧
    certificate_5_3 ∧
    certificate_5_4 ∧
    certificate_5_5 ∧
    certificate_5_6 ∧
    certificate_5_7 ∧
    certificate_5_8 ∧
    certificate_5_9 ∧
    certificate_5_10 ∧
    certificate_5_11 ∧
    certificate_5_13 ∧
    certificate_5_14 ∧
    certificate_5_15 ∧
    certificate_5_16 ∧
    certificate_5_17 ∧
    certificate_exercise_5_1 ∧
    certificate_exercise_5_2 ∧
    certificate_exercise_5_3 ∧
    certificate_exercise_5_4 ∧
    certificate_exercise_5_5 ∧
    certificate_exercise_5_6 ∧
    certificate_exercise_5_7 ∧
    certificate_exercise_5_8 ∧
    certificate_exercise_5_9 := by
  sorry

end Kyprianou.Ch05
