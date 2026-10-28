-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_stochasticIntegral_mul_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:01.338765+00:00
-- url     : https://prove2.me/theorems/0931c8b0-f5be-481f-ade1-da8d876465a1
-- title:
--   Stochastic Integral Stability Under Weight Replacement
-- statement:
--   This is an $L^2$ stability estimate for stochastic integrals with bounded integrand factor.
--
--   Let $P$ be a probability measure, $W$ a Brownian motion, and $\mathcal F$ a Brownian filtration for $W$. Let $u,v,H:\Omega\times\mathbb R\to\mathbb R$ be such that both products $uH$ and $vH$ are measurable and progressively measurable, and each has finite squared extended integral on every interval $[0,T]$ with $T>0$. Assume $C\ge0$ and $|H(\omega,s)|\le C$, and let $T>0$.
--
--   Then
--   $$
--   \int_\Omega\left|\int_0^T u_sH_s\,dW_s-\int_0^T v_sH_s\,dW_s\right|^2dP
--   \le
--   \operatorname{ofReal}(C^2)
--   \int_\Omega\int_{[0,T]}|u_s-v_s|^2\,ds\,dP.
--   $$
--
--   This estimate transfers an $L^2$ approximation of stochastic-integrand weights to an $L^2$ approximation of the corresponding stochastic integrals.
--
--   **Formalization Note** The integrals on the right are `ENNReal` integrals and the coefficient is embedded with `ENNReal.ofReal`; the stochastic integrals are `stochasticIntegralBrownian`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_stochasticIntegral_mul_sub_le
--       (u v : Ω → ℝ → ℝ)
--       (hmu : Measurable (Function.uncurry fun ω s => u ω s * H ω s))
--       (hpu : Probability.ProgressivelyMeasurable ℱ fun ω s => u ω s * H ω s)
--       (hqu : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖u ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hmv : Measurable (Function.uncurry fun ω s => v ω s * H ω s))
--       (hpv : Probability.ProgressivelyMeasurable ℱ fun ω s => v ω s * H ω s)
--       (hqv : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖v ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
--       {T : ℝ} (hT : 0 < T) :
--       ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => u ω s * H ω s) hmu hpu hqu T ω
--           - stochasticIntegralBrownian W ℱ hℱ (fun ω s => v ω s * H ω s) hmv hpv hqv T ω‖₊
--             : ℝ≥0∞) ^ 2 ∂P
--         ≤ ENNReal.ofReal (C ^ 2)
--           * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoRiemannIntegrand`](https://prove2.me/theorems/252cf557-7658-4111-b92a-8101844ab19c).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   [Source excerpt, lines 93–109](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoRiemannIntegrand.lean#L93-L109) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoRiemannIntegrand.lean#L91-L128 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoRiemannIntegrand`, declaration `LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoRiemannIntegrand

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoRiemannIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ

theorem LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le_readable
    (u v : Ω → ℝ → ℝ)
    (hmu : Measurable (Function.uncurry fun ω s => u ω s * H ω s))
    (hpu : Probability.ProgressivelyMeasurable ℱ fun ω s => u ω s * H ω s)
    (hqu : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖u ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmv : Measurable (Function.uncurry fun ω s => v ω s * H ω s))
    (hpv : Probability.ProgressivelyMeasurable ℱ fun ω s => v ω s * H ω s)
    (hqv : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖v ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => u ω s * H ω s) hmu hpu hqu T ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => v ω s * H ω s) hmv hpv hqv T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
