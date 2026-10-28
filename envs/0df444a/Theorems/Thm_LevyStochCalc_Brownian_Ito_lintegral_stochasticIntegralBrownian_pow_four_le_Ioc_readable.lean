-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_pow_four_le_Ioc_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:04.606244+00:00
-- url     : https://prove2.me/theorems/3c8eb92c-71e5-402e-87c0-a64cd8942cd0
-- title:
--   Fourth-Moment Bound for an Itô Integral Supported on an Interval
-- statement:
--   This theorem gives a fourth-moment bound for an $L^2$ Itô integral whose integrand is supported in $(a,b]$.
--
--   Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, and let $F:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable and progressively measurable. Assume:
--
--   1. the squared norm of $F$ has finite $[0,\infty]$-valued integral on every $[0,T]$ with $T>0$;
--   2. $C\ge0$ and $|F(\omega,s)|\le C$ for all $\omega,s$;
--   3. $0\le a<b$;
--   4. $F(\omega,s)=0$ whenever $s\notin(a,b]$.
--
--   Then
--
--   $$
--   \int^-\left\|\int_0^b F_s\,dW_s\right\|^4dP
--   \le \operatorname{ENNReal.ofReal}\!\left((6+\mathsf g_4)C^4(b-a)^2\right).
--   $$
--
--   The statement uses `stochasticIntegralBrownian`, `ENNReal.ofReal`, and an `ENNReal`-valued lintegral. It is the localized fourth-moment estimate for simple-integrand approximation and Fatou arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_stochasticIntegralBrownian_pow_four_le_Ioc
--       (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
--       (hp : Probability.ProgressivelyMeasurable ℱ F)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
--       {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
--       (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
--       ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
--         ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoIncrementMomentBounds`](https://prove2.me/theorems/c885777c-b44d-403b-b189-0d5182c90d15).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Selected supporting theorems: [`SimplePredictable.exists_restrict_Ioc`](https://prove2.me/theorems/5e9d641c-78ce-4154-aba8-1c8bbbf578e0), [`integral_partialSum_pow_four_le_varClock`](https://prove2.me/theorems/81999667-558b-4b27-9df9-47bbd1eb2a2d), [`SimplePredictable.lintegral_eval_sq_lt_top`](https://prove2.me/theorems/1a3d860d-d849-45a8-9155-ad2dbfbcdfa6), [`SimplePredictable.lintegral_pow_four_eq`](https://prove2.me/theorems/2e23b33c-826a-4615-a6b9-f62674c63f74), [`SimplePredictable.varClock_le_Ioc`](https://prove2.me/theorems/439559a5-0cc2-4a3a-a3c2-a6d24460420f).
--
--   Next: [`lintegral_stochasticIntegralBrownian_sub_pow_four_le`](https://prove2.me/theorems/65902486-10fb-4581-8867-4b4a6cc14280).
--
--   [Source excerpt, lines 55–64](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L55-L64) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L52-L203 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentBounds`, declaration `LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ

theorem LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc_readable
    (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
    (hp : Probability.ProgressivelyMeasurable ℱ F)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by sorry
