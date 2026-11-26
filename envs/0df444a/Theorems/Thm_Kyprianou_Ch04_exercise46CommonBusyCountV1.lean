-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46CommonBusyCountV1
-- name    : Kyprianou.Ch04.exercise46CommonBusyCountV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:14:19.823786+00:00
-- url     : https://prove2.me/theorems/a52f5034-8bcc-5fb4-80e5-8c7b4ecd687b
-- title:
--   One measurable count for physical and shifted busy-start sets
-- statement:
--   Use the common measurable drawdown kernel and the proved count functional. For the original process continuity of the supremum identifies its left workload with supremum minus the left limit; for shifted paths canonical membership follows by algebra.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46CommonBusyCountV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal =>
        sSup ((fun u => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w))) :
    ∃ C : (NNReal → Real) → ENNReal, Measurable C ∧
      (∀ᵐ w ∂P, C (fun t => L.X t w) =
        (({t : NNReal | 0 < t ∧ Wleft t w = 0 ∧
          0 < sSup ((fun u => L.X u w) '' Iic t) - L.X t w}).encard : ENNReal)) ∧
      (∀ w s, let Y : NNReal → Real := fun t => L.X (s+t) w - L.X s w
        C Y = (({t : NNReal | 0 < t ∧ sSup (Y '' Iic t) = Function.leftLim Y t ∧
          Y t < Function.leftLim Y t}).encard : ENNReal)) := by
  sorry
