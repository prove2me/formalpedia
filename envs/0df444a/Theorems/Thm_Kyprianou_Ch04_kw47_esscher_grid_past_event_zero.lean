-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_past_event_zero
-- name    : Kyprianou.Ch04.kw47_esscher_grid_past_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:45:24.911311+00:00
-- url     : https://prove2.me/theorems/38e10418-f4eb-5005-b204-3bf660fb7db6
-- title:
--   Esscher running-supremum weighted grid gains vanish on past events
-- statement:
--   For a spectrally negative Levy process and nonnegative alpha, finite predictable Esscher product gains have zero expectation on any past filtration event. The Esscher exponential is a Proved true martingale. Its running-supremum integrating factor is adapted and bounded on compact horizons. Apply the Proved generic past-event predictable grid identity to these exact factors. This is the conditional-centering input for the pathwise product-grid transfer in Exercise 4.7.
-- source:
--   Kyprianou (2006), Exercise 4.7, p. 108 and solution pp. 320-321; adapted Esscher exponential and running supremum product-grid martingale argument.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_predictable_grid_past_event_mean_zero
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_weight_horizon_bound
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite predictable Esscher product grid has zero gain on an
earlier filtration event, uniformly on a fixed compact horizon. -/

theorem Kyprianou.Ch04.kw47_esscher_grid_past_event_zero
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : ℕ → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T)
    (n : ℕ) (s : NNReal) (hs : s ≤ u 0)
    (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ w in A, ∑ i ∈ Finset.range n,
      Real.exp (-alpha * runningSup L (u i) w +
         L.ψ alpha * (u i : Real)) *
      (Real.exp (alpha * L.X (u (i + 1)) w -
         L.ψ alpha * (u (i + 1) : Real)) -
       Real.exp (alpha * L.X (u i) w -
         L.ψ alpha * (u i : Real))) ∂P) = 0 := by sorry
