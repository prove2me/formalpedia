-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_sub_sq_bochner_clamped_weighted_readable
-- name    : LevyStochCalc.Brownian.Ito.simpleIntegral_sub_sq_bochner_clamped_weighted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:58.171852+00:00
-- url     : https://prove2.me/theorems/9fca8288-f73b-4ee9-a521-8212a2c93f44
-- title:
--   Weighted Clamped Bochner Isometry
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, and let $H$ be a simple predictable integrand whose coefficient $H.\xi(i)$ is strongly measurable with respect to $\mathcal F_{H.\mathrm{partition}(i)}$. For $0\le s\le t$, let $g$ be strongly $\mathcal F_s$-measurable and suppose $|g(\omega)|\le C_g$ for every $\omega$. Put $c_i=\max\{s,\min\{H.\mathrm{partition}(i),t\}\}$. Then
--
--   $$\int g\,(I_t-I_s)^2\,dP
--   =\sum_i(c_{i+1}-c_i)\int g\,H.\xi(i)^2\,dP,$$
--
--   where $I_r=\mathrm{simpleIntegral}(W,H,r)$. The conclusion is a weighted, simple-level conditional Itô isometry; all displayed integrals are ordinary real integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma simpleIntegral_sub_sq_bochner_clamped_weighted
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {T : ℝ} (H : SimplePredictable Ω T)
--       (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (H.partition i.castSucc)) (H.ξ i))
--       {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
--       {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ s) g)
--       {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
--       ∫ ω, g ω * (simpleIntegral W H t ω - simpleIntegral W H s ω) ^ 2 ∂P
--         = ∑ i : Fin H.N,
--           (max s (min (H.partition i.succ) t) - max s (min (H.partition i.castSucc) t))
--             * ∫ ω, g ω * (H.ξ i ω) ^ 2 ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionCompensator`](https://prove2.me/theorems/11b95172-ce21-4778-ae54-6649149ee1fc).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integral_factor_increment_sq`](https://prove2.me/theorems/a261136e-59cf-42dc-be13-44c2ab2acb19), [`offDiagonal_increment_integral_zero_weighted`](https://prove2.me/theorems/f2dfb111-9070-47ca-850d-5692b6155761), [`simpleIntegral_sub_eq_clamp_sum`](https://prove2.me/theorems/5b6d9d87-e4ca-4af9-8b0b-701697a48c84).
--
--   Previous: [`simpleIntegral_sub_eq_clamp_sum`](https://prove2.me/theorems/5b6d9d87-e4ca-4af9-8b0b-701697a48c84) · Next: [`setIntegral_eval_sq_Icc_clamped`](https://prove2.me/theorems/264a25e4-219e-44a6-9deb-bfc553ff7dd9).
--
--   [Source excerpt, lines 175–189](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L175-L189) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L168-L281 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionCompensator`, declaration `LevyStochCalc.Brownian.Ito.simpleIntegral_sub_sq_bochner_clamped_weighted`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.simpleIntegral_sub_sq_bochner_clamped_weighted_readable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ s) g)
    {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
    ∫ ω, g ω * (simpleIntegral W H t ω - simpleIntegral W H s ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (max s (min (H.partition i.succ) t) - max s (min (H.partition i.castSucc) t))
          * ∫ ω, g ω * (H.ξ i ω) ^ 2 ∂P := by sorry
