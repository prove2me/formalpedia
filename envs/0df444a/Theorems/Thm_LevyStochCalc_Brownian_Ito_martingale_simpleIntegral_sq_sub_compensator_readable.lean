-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_simpleIntegral_sq_sub_compensator_readable
-- name    : LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:11.680348+00:00
-- url     : https://prove2.me/theorems/76ba9e80-d221-4784-b289-e962828cbbfd
-- title:
--   Simple-Level Compensated Square Martingale
-- statement:
--   This proves that the compensated square of a simple Brownian integral is a martingale. Let $P$ be a probability measure, let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, let $T>0$, and let $G$ be a simple predictable integrand on horizon $T$. Assume every coefficient $G.\xi(i)$ is strongly measurable with respect to $\mathcal F_{G.\mathrm{partition}(i)}$. Then the process
--
--   $$t\longmapsto \mathrm{simpleIntegral}(W,G,t)^2-
--   \int_{[0,t]}G.\mathrm{eval}(u,\cdot)^2\,du$$
--
--   is a martingale with respect to $\mathcal F$ and $P$. The compensator uses the interval $[0,t]$, which is empty when $t<0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma martingale_simpleIntegral_sq_sub_compensator
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {T : ℝ} (hT : 0 < T) (G : SimplePredictable Ω T)
--       (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (G.partition i.castSucc)) (G.ξ i)) :
--       MeasureTheory.Martingale
--         (fun t ω => (simpleIntegral W G t ω) ^ 2
--           - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
--         ℱ P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionCompensator`](https://prove2.me/theorems/11b95172-ce21-4778-ae54-6649149ee1fc).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`condExp_sq_increment_of_martingale`](https://prove2.me/theorems/9248f0a4-cf9c-4337-bd6c-ca5656254c6a), [`setIntegral_eval_sq_Icc_clamped`](https://prove2.me/theorems/264a25e4-219e-44a6-9deb-bfc553ff7dd9), [`simpleIntegral_sub_sq_bochner_clamped_weighted`](https://prove2.me/theorems/9fca8288-f73b-4ee9-a521-8212a2c93f44).
--
--   Previous: [`setIntegral_eval_sq_Icc_clamped`](https://prove2.me/theorems/264a25e4-219e-44a6-9deb-bfc553ff7dd9).
--
--   [Source excerpt, lines 329–339](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L329-L339) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L319-L585 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionCompensator`, declaration `LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator_readable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    MeasureTheory.Martingale
      (fun t ω => (simpleIntegral W G t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
      ℱ P := by sorry
