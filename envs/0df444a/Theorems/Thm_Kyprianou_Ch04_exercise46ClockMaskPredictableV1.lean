-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ClockMaskPredictableV1
-- name    : Kyprianou.Ch04.exercise46ClockMaskPredictableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:29:49.869696+00:00
-- url     : https://prove2.me/theorems/e18cdbaa-43bc-55a6-aa02-d66c1b0bb2f8
-- title:
--   First-arrival inclusive finite-horizon region is predictable
-- statement:
--   The inclusive stopping region is predictable, and intersecting it with the deterministic finite-horizon region preserves predictability.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ClockMaskPredictableV1
    {Omega : Type} [MeasurableSpace Omega]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) (T : NNReal) :
    MeasurableSet[G.rightCont.predictable]
      {p : NNReal × Omega | 0 < p.1 ∧ p.1 ≤ T ∧ (p.1 : WithTop NNReal) ≤ A p.2} := by
  sorry
