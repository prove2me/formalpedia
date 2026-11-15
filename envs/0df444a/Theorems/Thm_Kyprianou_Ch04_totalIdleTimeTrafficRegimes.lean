-- Prove2me | Theorems.Thm_Kyprianou_Ch04_totalIdleTimeTrafficRegimes
-- name    : Kyprianou.Ch04.totalIdleTimeTrafficRegimes
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:22:00.068691+00:00
-- url     : https://prove2.me/theorems/46e695e0-d53a-4ddf-8cf2-fa54ac9d62ca
-- title:
--   Theorem 4.1: total idle time law and traffic regimes
-- statement:
--   For a reflected spectrally negative bounded-variation input X=d t-S_t with d>0 and initial workload w≥0, total idle time I=integral 1{W=0} dt. If rho>1, I has atom 1-exp(-Phi(0)w) at zero and conditional positive part with Exp(d Phi(0)) tail, hence CDF exp(-Phi(0)w)*(1-exp(-d Phi(0)x)). If 0<rho≤1, I=+infinity a.s. The first-edition printed density misses factor d; this corrected law matches the proof. Traffic intensity is an extended nonnegative Levy jump-mass ratio, so infinite first moment is not silently classified as critical drift.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.1, printed page 89.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.1 (p. 89), using the normalised positive-density coefficient d*Phi(0). -/
theorem totalIdleTimeTrafficRegimes
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
                (1 - Real.exp (-phi * L.drift * x)))) ∧
    (0 < rho → rho ≤ 1 →
      (P {omega : Omega | totalIdle omega = ⊤}).toReal = 1) := by
  sorry
end Kyprianou.Ch04
