-- Prove2me | Theorems.Thm_Kyprianou_Ch04_totalIdleMeasurableV1
-- name    : Kyprianou.Ch04.totalIdleMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:14:27.526296+00:00
-- url     : https://prove2.me/theorems/144d86c3-786b-4614-a12e-e9bac5407f87
-- title:
--   Measurability of the raw infinite-horizon idle occupation
-- statement:
--   Apply the proved jointly measurable running supremum and input process results after identifying the raw sSup with the established runningSup. The measurable zero-workload indicator can then be integrated against restricted Lebesgue measure.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, proof of idle-time regulator identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
open Set

theorem Kyprianou.Ch04.totalIdleMeasurableV1
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
    Measurable totalIdle := by
  sorry
