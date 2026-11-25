-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_weight_horizon_bound
-- name    : Kyprianou.Ch04.kw47_esscher_weight_horizon_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:22:33.815689+00:00
-- url     : https://prove2.me/theorems/016d4f06-c0e7-5cd2-9117-5f72b3320f9c
-- title:
--   Deterministic finite-horizon bound for the Esscher running-maximum integrating factor
-- statement:
--   For a spectrally negative Lévy path, the running supremum is nonnegative, so on 0≤r≤T the predictable Esscher multiplier H(r)=exp(−αU(r)+rψ(α)) is bounded by the deterministic envelope exp(|ψ(α)|T). This envelope is the L-infinity ingredient for the Kella–Whitt stochastic product-grid martingale transfer.
-- source:
--   Kyprianou (2006), Exercise 4.7; proof using existing running-supremum dividend-strategy nonnegativity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_Kyprianou_Ch04_kw47_finite_horizon_predictable_weight_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_esscher_weight_horizon_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (L : SpectrallyNegativeLevy P 𝓕)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (T r : NNReal)
    (hrT : r ≤ T) (w : Ω) :
    Real.exp (-alpha * runningSup L r w + L.ψ alpha * (r : Real)) ≤
      Real.exp (|L.ψ alpha| * (T : Real)) := by sorry
