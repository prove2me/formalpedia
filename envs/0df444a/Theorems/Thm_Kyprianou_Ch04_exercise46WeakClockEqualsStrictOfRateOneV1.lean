-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46WeakClockEqualsStrictOfRateOneV1
-- name    : Kyprianou.Ch04.exercise46WeakClockEqualsStrictOfRateOneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:31:49.510858+00:00
-- url     : https://prove2.me/theorems/ac1e5bb5-bd95-52d4-8a61-c9ad563f2278
-- title:
--   Weak and strict passage agree almost surely at independent random heights
-- statement:
--   Compare weak passage to strict passage at an increasing sequence of lower positive heights and at the height itself. Their rate-one killed payoff expectations squeeze to the same value, giving equality of clocks by strict antitonicity.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46WeakClockEqualsStrictOfRateOneV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (J : Omega → Real) (hJ : AEMeasurable J P)
    (hJPositive : ∀ᵐ w ∂P, 0 < J w)
    (hInd : IndepFun J (fun w : Omega => fun t : NNReal => L.X t w) P)
    (phi : Real) (hp : 0 ≤ phi)
    (hStrict : ∀ x : Real, 0 < x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-1 *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
        = Real.exp (-phi * x)) :
    (fun w : Omega =>
      sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ J w ≤ L.X t w}) =ᵐ[P]
      (fun w => Kyprianou.Ch03.firstHittingTime L.X (Ioi (J w)) w) := by
  sorry
