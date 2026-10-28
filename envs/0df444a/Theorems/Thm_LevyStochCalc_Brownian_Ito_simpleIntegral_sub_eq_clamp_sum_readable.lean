-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_sub_eq_clamp_sum_readable
-- name    : LevyStochCalc.Brownian.Ito.simpleIntegral_sub_eq_clamp_sum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:29.089709+00:00
-- url     : https://prove2.me/theorems/5b6d9d87-e4ca-4af9-8b0b-701697a48c84
-- title:
--   Clamped Increment Expansion for Simple Integrals
-- statement:
--   For a Brownian motion $W$, a simple predictable integrand $H$, times $s\le t$, and $\omega\in\Omega$, define the clamped partition point $c_i=\max\{s,\min\{H.\mathrm{partition}(i),t\}\}$. The simple Itô integral satisfies
--
--   $$\mathrm{simpleIntegral}(W,H,t,\omega)-\mathrm{simpleIntegral}(W,H,s,\omega)
--   =\sum_{i\in\mathrm{Fin}(H.N)}H.\xi(i,\omega)\bigl(W_{c_{i+1}}(\omega)-W_{c_i}(\omega)\bigr).$$
--
--   The probability assumption on $P$ is part of the declaration, although the identity is pointwise. This provides the partition-level representation used in conditional Itô-isometry calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma simpleIntegral_sub_eq_clamp_sum
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       {T : ℝ} (H : SimplePredictable Ω T) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
--       simpleIntegral W H t ω - simpleIntegral W H s ω
--         = ∑ i : Fin H.N, H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
--             - W.W (max s (min (H.partition i.castSucc) t)) ω)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionCompensator`](https://prove2.me/theorems/11b95172-ce21-4778-ae54-6649149ee1fc).
--
--   Definition modules: [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Previous: [`offDiagonal_increment_integral_zero_weighted`](https://prove2.me/theorems/f2dfb111-9070-47ca-850d-5692b6155761) · Next: [`simpleIntegral_sub_sq_bochner_clamped_weighted`](https://prove2.me/theorems/9fca8288-f73b-4ee9-a521-8212a2c93f44).
--
--   [Source excerpt, lines 140–146](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L140-L146) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L134-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionCompensator`, declaration `LevyStochCalc.Brownian.Ito.simpleIntegral_sub_eq_clamp_sum`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.simpleIntegral_sub_eq_clamp_sum_readable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    simpleIntegral W H t ω - simpleIntegral W H s ω
      = ∑ i : Fin H.N, H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
          - W.W (max s (min (H.partition i.castSucc) t)) ω) := by sorry
