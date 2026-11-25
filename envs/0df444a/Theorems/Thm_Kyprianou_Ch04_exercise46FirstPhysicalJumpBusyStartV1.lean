-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstPhysicalJumpBusyStartV1
-- name    : Kyprianou.Ch04.exercise46FirstPhysicalJumpBusyStartV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:10:49.524084+00:00
-- url     : https://prove2.me/theorems/606d45a0-05be-5996-bb79-7d3f1541acba
-- title:
--   First physical jump begins a busy period for unit drift
-- statement:
--   The unit linear prefix has zero workload, so the left workload at the first jump is zero. A pre-jump value greater than the post-jump value witnesses strictly positive drawdown.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstPhysicalJumpBusyStartV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (hDrift : L.drift = 1)
    (w : Omega) (t : NNReal) (ht : 0 < t)
    (hJump : L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t)
    (hPrefix : ∀ s : NNReal, s < t → L.X s w = (s : Real))
    (hBound : ∀ s : NNReal, L.X s w ≤ (s : Real))
    (Wleft : Real)
    (hLeft : Tendsto
      (fun s : NNReal => sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w)
      (nhdsWithin t (Iio t)) (nhds Wleft)) :
    Wleft = 0 ∧ 0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w := by
  sorry
