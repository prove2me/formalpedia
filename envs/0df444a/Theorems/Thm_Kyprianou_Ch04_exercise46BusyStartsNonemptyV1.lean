-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartsNonemptyV1
-- name    : Kyprianou.Ch04.exercise46BusyStartsNonemptyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:47:59.214854+00:00
-- url     : https://prove2.me/theorems/a77870f0-6a00-5513-a7cb-23b49540eb5e
-- title:
--   First busy period exists almost surely for a positive finite arrival rate
-- statement:
--   Combine earliest physical jump existence, the exact pathwise drift-minus-jump identity on integer horizons, the nonnegative monotone drift deficit, and the established first busy-start lemma.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyStartsNonemptyV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (hRate : 0 < (L.ν (Iio (0 : Real))).toReal)
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal => sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w))) :
    let B : Omega → Set NNReal := fun w =>
      {t | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
    ∀ᵐ w ∂P, (B w).Nonempty := by
  sorry
