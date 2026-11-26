-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstPhysicalJumpClockV1
-- name    : Kyprianou.Ch04.exercise46FirstPhysicalJumpClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:33:46.015579+00:00
-- url     : https://prove2.me/theorems/5daa67ae-026a-488e-afe7-450025cfeb29
-- title:
--   Actual first negative jump clock is attained almost surely
-- statement:
--   The attained earliest physical negative jump agrees with the countable-infimum stopping clock.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstPhysicalJumpClockV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (hBV : L.BoundedVariation)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (hRate : 0 < (L.ν (Iio (0 : Real))).toReal) :
    let A : Omega → WithTop NNReal := fun w =>
      ⨅ u : NNReal, if 0 < u ∧
        L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u < 0
        then (u : WithTop NNReal) else ⊤
    let a : Omega → NNReal := fun w => (A w).untopD 0
    ∀ᵐ w ∂P, A w = (a w : WithTop NNReal) ∧ 0 < a w ∧
      L.X (a w) w < Function.leftLim (fun v : NNReal => L.X v w) (a w) ∧
      ∀ u : NNReal, 0 < u → u < a w →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u := by
  sorry
