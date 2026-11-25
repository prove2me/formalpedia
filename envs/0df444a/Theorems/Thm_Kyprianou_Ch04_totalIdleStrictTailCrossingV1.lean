-- Prove2me | Theorems.Thm_Kyprianou_Ch04_totalIdleStrictTailCrossingV1
-- name    : Kyprianou.Ch04.totalIdleStrictTailCrossingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:58:20.990297+00:00
-- url     : https://prove2.me/theorems/1900c001-25ab-45c4-8c8f-ccb8c8bdbc88
-- title:
--   Idle-time occupation strict tail equals upward crossing of the corresponding record level
-- statement:
--   The total idle time is measurable and, simultaneously at every nonnegative threshold x, exceeds x exactly when the input path crosses w+d*x. Prove the finite-horizon regulator identity d times idle occupation equals max(w,running supremum)-w, using the exact bounded-variation drift-minus-pure-jump representation and the absolutely continuous running maximum; then take the increasing horizon limit. This common pathwise step transfers the Chapter 3 upward first-passage law to both traffic regimes.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, p. 89, idle-time regulator identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.totalIdleStrictTailCrossingV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (w : Real) (hw : 0 ≤ w) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
    let W : NNReal → Omega → Real := fun t omega =>
      max w (supX t omega) - L.X t omega
    let totalIdle : Omega → ENNReal := fun omega =>
      ∫⁻ t in Set.Ici (0 : Real),
        (if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) ∂volume
    Measurable totalIdle ∧
    (∀ᵐ omega ∂P, ∀ x : Real, 0 ≤ x →
      (ENNReal.ofReal x < totalIdle omega ↔
        ∃ t : NNReal, w + L.drift * x < L.X t omega)) := by
  sorry
