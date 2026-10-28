-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_sq_increment_of_martingale_readable
-- name    : LevyStochCalc.Brownian.Ito.condExp_sq_increment_of_martingale_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:46.67353+00:00
-- url     : https://prove2.me/theorems/9248f0a4-cf9c-4337-bd6c-ca5656254c6a
-- title:
--   Conditional Pythagoras for Square-Integrable Martingales
-- statement:
--   This lemma gives the conditional Pythagorean identity for an $L^2$ martingale.
--
--   Let $P$ be a probability measure, let $\mathcal F$ be a filtration, and let $M_t:\Omega\to\mathbb R$ be a martingale with respect to $\mathcal F$ and $P$. For times $s\le t$, assume $M_s,M_t\in L^2(P)$. Then, almost everywhere with respect to $P$,
--
--   $$
--   \mathbb E\!\left[(M_t-M_s)^2\mid\mathcal F_s\right]
--   =\mathbb E\!\left[M_t^2\mid\mathcal F_s\right]-M_s^2.
--   $$
--
--   The conditional expectations are represented by `condExp`, and the equality is an almost-everywhere equality. This identity is a general tool for analyzing squared increments of square-integrable martingales.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma condExp_sq_increment_of_martingale
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
--       {M : ℝ → Ω → ℝ}
--       (hmart : MeasureTheory.Martingale M ℱ P)
--       {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
--       (hst : s ≤ t) :
--       P[(fun ω => (M t ω - M s ω) ^ 2) | ℱ s]
--         =ᵐ[P] fun ω => (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionConvergence`](https://prove2.me/theorems/7052eb64-0ceb-40e0-81f7-f59b0f13c887).
--
--   Previous: [`tendsto_eLpNorm_one_sq_sub`](https://prove2.me/theorems/f09a6b4b-92fc-4d7f-afe6-745f7f468f5b) · Next: [`integral_factor_increment_sq`](https://prove2.me/theorems/a261136e-59cf-42dc-be13-44c2ab2acb19).
--
--   [Source excerpt, lines 301–309](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L301-L309) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L298-L360 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionConvergence`, declaration `LevyStochCalc.Brownian.Ito.condExp_sq_increment_of_martingale`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.condExp_sq_increment_of_martingale_readable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    P[(fun ω => (M t ω - M s ω) ^ 2) | ℱ s]
      =ᵐ[P] fun ω => (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2 := by sorry
