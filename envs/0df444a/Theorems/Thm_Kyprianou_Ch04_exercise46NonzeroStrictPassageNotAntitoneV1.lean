-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46NonzeroStrictPassageNotAntitoneV1
-- name    : Kyprianou.Ch04.exercise46NonzeroStrictPassageNotAntitoneV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T21:27:36.696076+00:00
-- url     : https://prove2.me/theorems/69fe9097-25b0-43b0-8bff-036fb4a5e8c2
-- title:
--   A nonzero positive-level killed transform rules out antitone paths
-- statement:
--   An antitone path started at zero never strictly crosses level one. If paths were antitone almost surely the killed expectation would be zero.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46NonzeroStrictPassageNotAntitoneV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (beta : Real)
    (hNonzero : (∫ w,
      if Kyprianou.Ch03.firstHittingTime L.X (Ioi (1 : Real)) w = ⊤
      then (0 : Real) else Real.exp (-beta *
        (((Kyprianou.Ch03.firstHittingTime L.X (Ioi (1 : Real)) w).untopD 0 : NNReal) : Real))
      ∂P) ≠ 0) :
    ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)) := by
  sorry
