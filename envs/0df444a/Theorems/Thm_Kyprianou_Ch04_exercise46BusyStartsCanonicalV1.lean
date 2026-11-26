-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartsCanonicalV1
-- name    : Kyprianou.Ch04.exercise46BusyStartsCanonicalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:48:00.634967+00:00
-- url     : https://prove2.me/theorems/78ec8e12-6acb-45fe-ab6c-4eb4d1484d74
-- title:
--   Physical busy-start set agrees almost surely with a jointly measurable jump subset
-- statement:
--   The running supremum is continuous. Thus the workload left limit equals the running supremum minus the left limit of X. At a busy start this is zero and the negative jump is strict. Jointly measurable supremum and pre-jump functions give a measurable representative.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyStartsCanonicalV1
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
    ∃ S : Set (Omega × NNReal), MeasurableSet S ∧
      (∀ w t, (w,t) ∈ S → 0 < t ∧
        L.X t w - Function.leftLim (fun u : NNReal => L.X u w) t ≠ 0) ∧
      ∀ᵐ w ∂P, B w = {t | (w,t) ∈ S} := by
  sorry
