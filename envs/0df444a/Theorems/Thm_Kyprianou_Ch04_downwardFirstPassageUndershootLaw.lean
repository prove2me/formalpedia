-- Prove2me | Theorems.Thm_Kyprianou_Ch04_downwardFirstPassageUndershootLaw
-- name    : Kyprianou.Ch04.downwardFirstPassageUndershootLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T22:26:48.606585+00:00
-- url     : https://prove2.me/theorems/3c67d26d-16a0-4303-aa7e-803932c50db1
-- title:
--   Corollary 4.12: downward passage probability and deficit law
-- statement:
--   For spectrally negative bounded-variation X with positive drift d and positive mean psi'(0+), the strict downward-passage probability is rho = (d-psi'(0+))/d. The joint probability of ruin with deficit at most x equals the integrated absolute-negative-jump tail divided by d. When rho>0, the conditional deficit CDF given ruin equals the same tail divided by d*rho. The joint law remains meaningful when rho=0; no conditional distribution is asserted on a zero-probability event.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.12, printed page 105.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Corollary 4.12 (p. 105), including the conditional deficit distribution. -/
theorem downwardFirstPassageUndershootLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (hMeanPositive :
      0 < derivWithin L.ψ (Set.Ici (0 : Real)) 0) :
    let tau : Omega → WithTop NNReal := fun omega =>
      Kyprianou.Ch03.firstHittingTime L.X (Set.Iio 0) omega
    let rho : Real :=
      (L.drift - derivWithin L.ψ (Set.Ici (0 : Real)) 0) /
        L.drift
    (P {omega : Omega | tau omega ≠ ⊤}).toReal = rho ∧
    (∀ (finiteTime : Omega → NNReal),
      (∀ omega : Omega, tau omega ≠ ⊤ →
        tau omega = (finiteTime omega : WithTop NNReal)) →
      ∀ x : Real, 0 ≤ x →
        let ruinAndDeficit : Set Omega :=
          {omega : Omega |
            tau omega ≠ ⊤ ∧
              -(L.X (finiteTime omega) omega) ≤ x}
        let integratedTail : Real :=
          ∫ y in Set.Icc (0 : Real) x,
            (L.ν (Set.Iio (-y))).toReal ∂volume
        (P ruinAndDeficit).toReal =
          (1 / L.drift) * integratedTail ∧
        (0 < rho →
          (P ruinAndDeficit).toReal / rho =
            (1 / (L.drift * rho)) * integratedTail)) := by
  sorry
end Kyprianou.Ch04
