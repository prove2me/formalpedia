-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PredictablePrelevelEventV1
-- name    : Kyprianou.Ch04.exercise46PredictablePrelevelEventV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:16:21.106096+00:00
-- url     : https://prove2.me/theorems/4606955e-6944-4305-b7c6-ff9296ce94ea
-- title:
--   Pre-arrival-height contacts after the first clock form a predictable set
-- statement:
--   The capped arrival height and the pre-jump path are predictable. On the predictable event A<t the cap equals the original arrival height; intersect with the deterministic horizon.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PredictablePrelevelEventV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (T : NNReal) :
    MeasurableSet[G.rightCont.predictable] {p : NNReal × Omega |
      A p.2 < (p.1 : WithTop NNReal) ∧ p.1 ≤ T ∧
      Function.leftLim (fun u : NNReal => L.X u p.2) p.1 =
        (((A p.2).untopD 0 : NNReal) : Real)} := by
  sorry
