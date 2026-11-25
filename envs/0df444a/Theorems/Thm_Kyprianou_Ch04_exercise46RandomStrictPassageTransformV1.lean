-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RandomStrictPassageTransformV1
-- name    : Kyprianou.Ch04.exercise46RandomStrictPassageTransformV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:27:36.887799+00:00
-- url     : https://prove2.me/theorems/ac0a01a9-49c6-4807-9f13-040bc94349d1
-- title:
--   Strict first passage at an independent positive random height
-- statement:
--   Use the measurable coordinate-path kernel and product-law Fubini. The fixed-height Laplace identity integrates over the random height; measurability follows from the kernel representation.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RandomStrictPassageTransformV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (J : Omega → Real) (hJ : AEMeasurable J P)
    (hJPositive : ∀ᵐ w ∂P, 0 < J w)
    (hInd : IndepFun J (fun w : Omega => fun t : NNReal => L.X t w) P)
    (beta phi : Real) (hb : 0 ≤ beta)
    (hStrict : ∀ x : Real, 0 < x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-beta *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
        = Real.exp (-phi * x)) :
    let S : Omega → WithTop NNReal := fun w =>
      Kyprianou.Ch03.firstHittingTime L.X (Ioi (J w)) w
    AEMeasurable S P ∧
      (∫ w, if S w = ⊤ then (0 : Real)
        else Real.exp (-beta * (((S w).untopD 0 : NNReal) : Real)) ∂P) =
      ∫ w, Real.exp (-phi * J w) ∂P := by
  sorry
