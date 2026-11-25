-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleOccupationIntegrandMeasurableV1
-- name    : Kyprianou.Ch04.idleOccupationIntegrandMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:24:18.998117+00:00
-- url     : https://prove2.me/theorems/1bfc32f1-61df-4625-b0ac-67bf6bc99ac5
-- title:
--   Idle occupation integrand measurable for each input path
-- statement:
--   Use joint measurability of the original input and running supremum, and identify the running supremum with the raw finite-path supremum. Compose with the time map and take the indicator of the zero workload.
-- source:
--   Kyprianou (2006), Theorem 4.1, occupation measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.idleOccupationIntegrandMeasurableV1
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
    ∀ omega : Omega, Measurable (fun t : Real =>
      if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) := by
  sorry
