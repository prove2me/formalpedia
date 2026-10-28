-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_pow_four_succ_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_succ_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:26.714262+00:00
-- url     : https://prove2.me/theorems/8d6ebf13-04ca-46c7-8946-0ee73126e99a
-- title:
--   Fourth-Moment Recursion for Partial Sums
-- statement:
--   This theorem gives the one-step fourth-moment recursion for the partial sums of a simple predictable Brownian integral.
--
--   Let $G$ be a simple predictable integrand with strongly measurable coefficients, let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, and assume:
--
--   1. $C\ge0$;
--   2. every coefficient satisfies $|\xi_i(\omega)|\le C$;
--   3. $k<N$, where $N$ is the number of tiles.
--
--   Writing $\tau_k$ for the partition times and $\mathsf g_4$ for `gaussianFourthMoment`,
--
--   $$
--   \begin{aligned}
--   \int (S_{k+1})^4\,dP
--   ={}&\int (S_k)^4\,dP
--   +6(\tau_{k+1}-\tau_k)\int S_k^2\xi_k^2\,dP\\
--   &+(\tau_{k+1}-\tau_k)^2\mathsf g_4\int \xi_k^4\,dP,
--   \end{aligned}
--   $$
--
--   where $S_k=\texttt{G.partialSum}(W,k)$ and $\xi_k$ is the coefficient on the $k$th tile. This identity is the elementary recursion used to derive fourth-moment bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito.SimplePredictable`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_partialSum_pow_four_succ {k : ℕ} (hk : k < G.N) :
--       ∫ ω, (G.partialSum W (k + 1) ω) ^ 4 ∂P
--         = (∫ ω, (G.partialSum W k ω) ^ 4 ∂P)
--           + 6 * ((∫ ω, (G.partialSum W k ω) ^ 2 * (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
--             * (G.partition (⟨k, hk⟩ : Fin G.N).succ
--               - G.partition (⟨k, hk⟩ : Fin G.N).castSucc))
--           + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 4 ∂P)
--             * ((G.partition (⟨k, hk⟩ : Fin G.N).succ
--               - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ^ 2 * gaussianFourthMoment)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentPartialSums`](https://prove2.me/theorems/705e75c1-4971-40ae-82c1-068282421322).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`stronglyMeasurable_partialSum`](https://prove2.me/theorems/fd1cc025-8f0a-4737-8e80-8b55eaf193de), [`integral_add_mul_increment_pow_four`](https://prove2.me/theorems/70cfa191-ba5b-406e-9b47-0bc6e678c599).
--
--   Previous: [`integral_partialSum_sq_succ`](https://prove2.me/theorems/9bf4edcb-e687-4a69-83b1-87842c0ed837) · Next: [`integral_partialSum_sq_le_varClock`](https://prove2.me/theorems/2ab4ca54-1962-4f62-bd70-5633cdf86d27).
--
--   [Source excerpt, lines 254–262](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L254-L262) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L252-L273 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentPartialSums`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_succ`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_succ_readable {k : ℕ} (hk : k < G.N) :
    ∫ ω, (G.partialSum W (k + 1) ω) ^ 4 ∂P
      = (∫ ω, (G.partialSum W k ω) ^ 4 ∂P)
        + 6 * ((∫ ω, (G.partialSum W k ω) ^ 2 * (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
          * (G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc))
        + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 4 ∂P)
          * ((G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ^ 2 * gaussianFourthMoment) := by sorry
