-- Prove2me | Theorems.Thm_Kyprianou_Ch04_totalIdleTraffic_supercriticalFiniteIdle
-- name    : Kyprianou.Ch04.totalIdleTraffic_supercriticalFiniteIdle
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T13:03:17.517779+00:00
-- url     : https://prove2.me/theorems/b30d1c74-aea0-45d4-b73a-ead68dfeda8c
-- title:
--   totalIdleTimeTrafficRegimesV2: Positive-traffic-parameter finite idle-time distribution, full source corrected density
-- statement:
--   Positive-traffic-parameter finite idle-time distribution, full source corrected density. An exact standalone source conjunct from the complete corrected Chapter 4 theorem, retaining all original binders and assumptions.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Theorem 4.1, printed p. 89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.1 (p. 89), using the normalised positive-density coefficient d*Phi(0). -/
theorem totalIdleTraffic_supercriticalFiniteIdle
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
    (rho > 1 →
      ∃ phi : Real,
        0 < phi ∧ L.ψ phi = 0 ∧
        (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
        (P {omega : Omega | totalIdle omega = 0}).toReal =
          1 - Real.exp (-phi * w) ∧
        (∀ x : Real, 0 ≤ x →
          (P {omega : Omega |
            0 < totalIdle omega ∧
            totalIdle omega ≤ ENNReal.ofReal x}).toReal =
              Real.exp (-phi * w) *
                (1 - Real.exp (-phi * L.drift * x)))) := by
  sorry
end Kyprianou.Ch04
