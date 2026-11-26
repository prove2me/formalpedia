-- Prove2me | Theorems.Thm_Kyprianou_Ch04_downwardPassageFiniteProbabilityBV
-- name    : Kyprianou.Ch04.downwardPassageFiniteProbabilityBV
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:02:03.190106+00:00
-- url     : https://prove2.me/theorems/7411f209-7dba-4242-a357-5c44726cffca
-- title:
--   Downward first-passage probability from BV Levy drift and positive mean
-- statement:
--   For a bounded-variation spectrally negative Levy process of positive drift and positive mean, the probability of strict downward passage is (d-psi-prime-zero)/d.
-- source:
--   Kyprianou (2006), Corollary 4.12, page 105, total ruin mass.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.downwardPassageFiniteProbabilityBV
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
    (P {omega : Omega | tau omega ≠ ⊤}).toReal = rho := by
  sorry
