-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FixedStrictRootTransformV1
-- name    : Kyprianou.Ch04.exercise46FixedStrictRootTransformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T10:45:45.64909+00:00
-- url     : https://prove2.me/theorems/51cfc206-98f1-4c85-896c-8c82b43ae3e4
-- title:
--   Strict passage at the prescribed largest nonnegative root
-- statement:
--   Use the proved chapter 3 first-passage transform at zero discount. The two largest-root conditions identify the returned root with phi.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FixedStrictRootTransformV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hnd : ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)))
    (phi : Real) (hphi : 0 < phi) (hroot : L.ψ phi = 0)
    (hmax : ∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) :
    ∀ x : Real, 0 ≤ x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-(0 : Real) *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
      = Real.exp (-phi * x) := by
  sorry
