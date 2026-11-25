-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RandomWeakPassageTransformV1
-- name    : Kyprianou.Ch04.exercise46RandomWeakPassageTransformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T21:02:24.89364+00:00
-- url     : https://prove2.me/theorems/545c88be-a9b0-49b1-a274-8d5765ad6346
-- title:
--   Independent positive random level weak first-passage transform
-- statement:
--   Derive the defective weak passage transform and an almost-everywhere measurable clock by sandwiching weak passage between strict passages at nearby positive levels, using right-continuous rational observations and independence of the level and the path.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RandomWeakPassageTransformV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (service : Measure Real) [IsProbabilityMeasure service]
    (J : Omega → Real) (hJLaw : P.map J = service)
    (hJPositive : ∀ᵐ omega ∂P, 0 < J omega)
    (hIndependent : Indep
      (MeasurableSpace.comap J inferInstance)
      (MeasurableSpace.comap (fun omega : Omega => fun t : NNReal => L.X t omega)
        inferInstance) P)
    (beta phi : Real) (hb : 0 ≤ beta) (hp : 0 ≤ phi)
    (hStrict : ∀ x : Real, 0 ≤ x →
      (∫ omega, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) omega = ⊤
        then (0 : Real) else Real.exp (-beta *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) omega).untopD 0 : NNReal) : Real)) ∂P)
        = Real.exp (-phi * x)) :
    let B : Omega → WithTop NNReal := fun omega =>
      sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ J omega ≤ L.X t omega}
    AEMeasurable B P ∧
      (∫ omega, if B omega = ⊤ then (0 : Real)
        else Real.exp (-beta * (((B omega).untopD 0 : NNReal) : Real)) ∂P) =
      ∫ y : Real, Real.exp (-phi * y) ∂service := by
  sorry
