-- Prove2me | Theorems.Thm_Kyprianou_Ch04_totalIdleTraffic_nonSupercriticalInfiniteIdle
-- name    : Kyprianou.Ch04.totalIdleTraffic_nonSupercriticalInfiniteIdle
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T13:03:08.665363+00:00
-- url     : https://prove2.me/theorems/7c067fbd-6878-408d-8b59-4b4282eb7e3a
-- title:
--   totalIdleTimeTrafficRegimesV2: Low-traffic-parameter infinite total idle time, including the zero-traffic limit
-- statement:
--   Low-traffic-parameter infinite total idle time, including the zero-traffic limit. An exact standalone source conjunct from the complete corrected Chapter 4 theorem, retaining all original binders and assumptions.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Theorem 4.1, printed p. 89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.1 (p. 89), using the normalised positive-density coefficient d*Phi(0). -/
theorem totalIdleTraffic_nonSupercriticalInfiniteIdle
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
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    (rho ≤ 1 →
      (P {omega : Omega | totalIdle omega = ⊤}).toReal = 1) := by
  sorry
end Kyprianou.Ch04
