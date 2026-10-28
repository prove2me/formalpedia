-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_pow_four_le_varClock_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le_varClock_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:03.801054+00:00
-- url     : https://prove2.me/theorems/81999667-558b-4b27-9df9-47bbd1eb2a2d
-- title:
--   Fourth-Moment Bound by the Variance Clock
-- statement:
--   This theorem bounds the fourth moment of a partial elementary Brownian integral using per-tile variance budgets.
--
--   Let $G$ be a simple predictable integrand, $W$ a Brownian motion with Brownian filtration $\mathcal F$, and assume:
--
--   1. the coefficients are strongly measurable;
--   2. $C\ge0$ and $|\xi_i(\omega)|\le C$;
--   3. $|\xi_i(\omega)|\le c_i$ for a family $c_i$;
--   4. $k\le N$.
--
--   Then
--
--   $$
--   \int \bigl(G.\operatorname{partialSum}(W,k)\bigr)^4\,dP
--   \le 6\,V_NV_k+\mathsf g_4 V_k^2,
--   $$
--
--   where $V_r=\operatorname{varClock}(G,c,r)$ and $\mathsf g_4$ is `gaussianFourthMoment`. This is the sharper partial-sum fourth-moment estimate in terms of elapsed variance rather than a uniform time bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito.SimplePredictable`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_partialSum_pow_four_le_varClock {c : Fin G.N → ℝ}
--       (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
--       ∀ (k : ℕ) (_hk : k ≤ G.N),
--         ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
--           ≤ 6 * (G.varClock c G.N * G.varClock c k)
--             + gaussianFourthMoment * G.varClock c k ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentPartialSums`](https://prove2.me/theorems/705e75c1-4971-40ae-82c1-068282421322).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integral_partialSum_pow_four_succ`](https://prove2.me/theorems/8d6ebf13-04ca-46c7-8946-0ee73126e99a), [`integral_partialSum_sq_le_varClock`](https://prove2.me/theorems/2ab4ca54-1962-4f62-bd70-5633cdf86d27), [`varClock_mono`](https://prove2.me/theorems/ca4d3739-0c25-400e-91e5-2326905bc735).
--
--   Previous: [`integral_partialSum_sq_le_varClock`](https://prove2.me/theorems/2ab4ca54-1962-4f62-bd70-5633cdf86d27).
--
--   [Source excerpt, lines 464–469](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L464-L469) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L461-L522 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentPartialSums`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le_varClock`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le_varClock_readable {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
        ≤ 6 * (G.varClock c G.N * G.varClock c k)
          + gaussianFourthMoment * G.varClock c k ^ 2 := by sorry
