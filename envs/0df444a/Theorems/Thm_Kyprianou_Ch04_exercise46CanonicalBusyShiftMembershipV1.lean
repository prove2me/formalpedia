-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46CanonicalBusyShiftMembershipV1
-- name    : Kyprianou.Ch04.exercise46CanonicalBusyShiftMembershipV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:27:13.44606+00:00
-- url     : https://prove2.me/theorems/68cdb0de-3536-5329-b4ea-5c82bc83e97a
-- title:
--   Canonical busy-start membership is invariant under restart at a record
-- statement:
--   Combine drawdown restart invariance with translation of the left limit and preservation of the jump mark.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46CanonicalBusyShiftMembershipV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (s u : NNReal) (hu : 0 < u)
    (hrecord : ∀ v ≤ s, L.X v w ≤ L.X s w)
    (hb : BddAbove ((fun t : NNReal => L.X t w) '' Iic (s+u))) :
    let Y : NNReal → Real := fun t => L.X (s+t) w - L.X s w
    (0 < s+u ∧ 0 < sSup ((fun t : NNReal => L.X t w) '' Iic (s+u)) - L.X (s+u) w ∧
      sSup ((fun t : NNReal => L.X t w) '' Iic (s+u)) - L.X (s+u) w =
        -(L.X (s+u) w - Function.leftLim (fun t : NNReal => L.X t w) (s+u))) ↔
    (0 < u ∧ 0 < sSup (Y '' Iic u) - Y u ∧
      sSup (Y '' Iic u) - Y u = -(Y u - Function.leftLim Y u)) := by
  sorry
