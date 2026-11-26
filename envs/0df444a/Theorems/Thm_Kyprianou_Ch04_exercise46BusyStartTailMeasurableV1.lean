-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartTailMeasurableV1
-- name    : Kyprianou.Ch04.exercise46BusyStartTailMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:48:00.587866+00:00
-- url     : https://prove2.me/theorems/a1c1d460-de52-43ef-af6f-6b5fdd62475d
-- title:
--   Physical busy-start tail events have measurable representatives
-- statement:
--   Identify the busy starts with the canonical jointly measurable jump subset on the almost-sure common path event. Apply the measurable jump subset count and take its superlevel sets.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyStartTailMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal => sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w))) :
    let B : Omega → Set NNReal := fun w =>
      {t | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
    ∀ k : Nat, ∃ S : Set Omega, MeasurableSet S ∧
      S =ᵐ[P] {w | ((k+1 : Nat) : ENat) ≤ (B w).encard} := by
  sorry
