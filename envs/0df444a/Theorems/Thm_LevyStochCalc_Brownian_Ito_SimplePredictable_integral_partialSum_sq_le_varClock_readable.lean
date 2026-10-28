-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_sq_le_varClock_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_sq_le_varClock_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:35.22499+00:00
-- url     : https://prove2.me/theorems/2ab4ca54-1962-4f62-bd70-5633cdf86d27
-- title:
--   Second-Moment Bound by the Variance Clock
-- statement:
--   This theorem bounds the second moment of every partial sum by its coefficient variance budget.
--
--   Let $G$ be a simple predictable integrand, $W$ a Brownian motion with Brownian filtration $\mathcal F$, and assume the coefficients are strongly measurable. Let $C\ge0$, assume $|\xi_i(\omega)|\le C$, and let $c_i$ be another coefficient bound satisfying $|\xi_i(\omega)|\le c_i$ for every tile $i$ and outcome $\omega$. For every $k\le N$,
--
--   $$
--   \int \bigl(G.\operatorname{partialSum}(W,k)\bigr)^2\,dP
--   \le \operatorname{varClock}(G,c,k).
--   $$
--
--   Here `SimplePredictable.varClock` is the finite sum of $c_i^2(\tau_{i+1}-\tau_i)$ over the first $k$ tiles. The theorem is a reusable $L^2$ estimate with per-tile rather than uniform coefficient bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito.SimplePredictable`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_partialSum_sq_le_varClock {c : Fin G.N → ℝ}
--       (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
--       ∀ (k : ℕ) (_hk : k ≤ G.N),
--         ∫ ω, (G.partialSum W k ω) ^ 2 ∂P ≤ G.varClock c k
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentPartialSums`](https://prove2.me/theorems/705e75c1-4971-40ae-82c1-068282421322).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integral_partialSum_sq_succ`](https://prove2.me/theorems/9bf4edcb-e687-4a69-83b1-87842c0ed837).
--
--   Previous: [`integral_partialSum_pow_four_succ`](https://prove2.me/theorems/8d6ebf13-04ca-46c7-8946-0ee73126e99a) · Next: [`integral_partialSum_pow_four_le_varClock`](https://prove2.me/theorems/81999667-558b-4b27-9df9-47bbd1eb2a2d).
--
--   [Source excerpt, lines 438–441](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L438-L441) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L436-L459 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentPartialSums`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_sq_le_varClock`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
include hℱ h_adapt hC0 hC

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_sq_le_varClock_readable {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 2 ∂P ≤ G.varClock c k := by sorry
