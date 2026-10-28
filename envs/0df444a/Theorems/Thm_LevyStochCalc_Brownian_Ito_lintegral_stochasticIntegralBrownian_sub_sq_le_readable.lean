-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_sq_le_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:13.379987+00:00
-- url     : https://prove2.me/theorems/0e7c5bb8-1257-4ddd-a411-f3d6af20e053
-- title:
--   Second-Moment Bound for a Bounded Itô-Integral Increment
-- statement:
--   This proves the second-moment estimate for an increment of a scalar Brownian Itô integral.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $W$ be a Brownian motion, and let $\mathcal F$ be a Brownian filtration. Let $H:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable and progressively measurable, with finite `ENNReal` energy on every positive horizon. Suppose that for some $C\ge0$,
--   $$
--   |H(\omega,s)|\le C
--   $$
--   for every $\omega,s$. Let $0\le a<b$. Then
--   $$
--   \int_\Omega
--   \left\|I_b[H](\omega)-I_a[H](\omega)\right\|_+^2\,dP
--   \le
--   \operatorname{ofReal}\!\left(C^2(b-a)\right).
--   $$
--
--   The left side is an `ENNReal` integral, and the right side is the `ENNReal.ofReal` coercion of the real quantity $C^2(b-a)$. This is the basic variance-type increment estimate used in subsequent moment bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_stochasticIntegralBrownian_sub_sq_le
--       (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
--       (hp : Probability.ProgressivelyMeasurable ℱ H)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
--       {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
--           - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
--         ≤ ENNReal.ofReal (C ^ 2 * (b - a))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoIncrementMomentBounds`](https://prove2.me/theorems/c885777c-b44d-403b-b189-0d5182c90d15).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stochasticIntegralBrownian_indicator_Ioc`](https://prove2.me/theorems/bcc8c011-e83f-4b9e-a0e6-5de008451e39).
--
--   Previous: [`lintegral_stochasticIntegralBrownian_sub_pow_four_le`](https://prove2.me/theorems/65902486-10fb-4581-8867-4b4a6cc14280) · Next: [`integral_sub_pow_four_le`](https://prove2.me/theorems/12ff2533-d8a3-4978-a4f3-a45469d7fa7c).
--
--   [Source excerpt, lines 292–301](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L292-L301) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L289-L355 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentBounds`, declaration `LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_sq_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_sq_le_readable
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2 * (b - a)) := by sorry
