-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstMarkedCountPathV1
-- name    : Kyprianou.Ch04.exercise46FirstMarkedCountPathV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:17:49.367024+00:00
-- url     : https://prove2.me/theorems/b5e23f6b-c653-481b-9648-30322444f5cc
-- title:
--   Physical marked count stopped at first jump is a singleton indicator
-- statement:
--   The mark-count preimage is the singleton first jump time if it is before the horizon and has a selected mark; otherwise it is empty.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstMarkedCountPathV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (a T : NNReal) (ha : 0 < a)
    (hJ : L.X a w - Function.leftLim (fun u : NNReal => L.X u w) a ≠ 0)
    (hBefore : ∀ t : NNReal, 0 < t → t < a →
      L.X t w = Function.leftLim (fun u : NNReal => L.X u w) t)
    (B : Set Real) (hB : MeasurableSet B) :
    let NX := ((Measure.count.restrict {u : NNReal | 0 < u ∧
      L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
      (fun u : NNReal => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    NX (Ioc 0 (min a T) ×ˢ B) =
      @ite ENNReal (a ≤ T ∧ L.X a w - Function.leftLim (fun u : NNReal => L.X u w) a ∈ B)
        (Classical.propDecidable _) 1 0 := by
  sorry
