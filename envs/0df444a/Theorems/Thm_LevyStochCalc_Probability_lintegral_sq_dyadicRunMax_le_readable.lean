-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_readable
-- name    : LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:03.669983+00:00
-- url     : https://prove2.me/theorems/c1b80434-c26c-49be-a883-841d52382ee6
-- title:
--   Dyadic $L^2$ Maximal Bound for a Martingale
-- statement:
--   This is a dyadic $L^2$ maximal inequality for a continuous-time martingale sampled at dyadic times.
--
--   Let $(\Omega,\mathcal F,P)$ be a finite probability space, let $M:\mathbb R\to\Omega\to\mathbb R$ be a martingale relative to a filtration $\mathcal F$, and let $T\ge0$. For every $n\in\mathbb N$, let `dyadicRunMax M T n` be the running maximum along the dyadic partition of $[0,T]$ at level $n$.
--
--   $$\int_\Omega \bigl\|\operatorname{dyadicRunMax}(M,T,n)(\omega)\bigr\|^2\,dP(\omega)\le 4\int_\Omega |M_T(\omega)|^2\,dP(\omega).$$
--
--   The integrals are `ENNReal` lower integrals, and the norm is represented by the nonnegative norm coercion. The estimate is intended for dyadic maximal-control arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_dyadicRunMax_le {μ : Measure Ω} [IsFiniteMeasure μ]
--       {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) (n : ℕ) :
--       ∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
--         ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Supporting theorems: [`maximal_ineq_Lp`](https://prove2.me/theorems/3d6a746c-5b37-4dc6-83c9-71b26ca49833).
--
--   Previous: [`iSup_enorm_eq_iSup_dyadicRunMax`](https://prove2.me/theorems/acb0a4f1-b242-45cd-80de-139b129bb826) · Next: [`sq_sum_le_card_sq_mul`](https://prove2.me/theorems/7c556d30-1476-4749-9b82-7ef598da576d).
--
--   [Source excerpt, lines 268–271](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/DoobContinuous.lean#L268-L271) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L267-L291 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}

theorem LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le_readable {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) (n : ℕ) :
    ∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by sorry
