-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_neg_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:50.130487+00:00
-- url     : https://prove2.me/theorems/5492f889-dcf9-4710-b8c2-bd3dcd30d16a
-- title:
--   Negation of the Itô Integral
-- statement:
--   This proves linearity of the Brownian Itô integral under negation.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $W$ be a Brownian motion, and let $\mathcal F$ be a Brownian filtration. For an integrand $H:\Omega\times\mathbb R\to\mathbb R$, assume both $H$ and $-H$ are jointly measurable, progressively measurable, and have finite `ENNReal` $L^2$ energy on every positive interval:
--   $$
--   \int_\Omega\int_{[0,T]}\|H(\omega,s)\|_+^2\,ds\,dP<\top,
--   \qquad
--   \int_\Omega\int_{[0,T]}\|-H(\omega,s)\|_+^2\,ds\,dP<\top.
--   $$
--   For every $T>0$, the integral of the negated integrand equals the negation of the integral, $P$-almost everywhere:
--   $$
--   I_T[-H](\omega)=-I_T[H](\omega).
--   $$
--
--   This is the negation case used to derive subtractive and finite-sum linearity.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_neg {H : Ω → ℝ → ℝ}
--       (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hmn : Measurable (Function.uncurry fun ω s => -H ω s))
--       (hpn : Probability.ProgressivelyMeasurable ℱ fun ω s => -H ω s)
--       (hqn : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖-H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {T : ℝ} (hT : 0 < T) :
--       stochasticIntegralBrownian W ℱ hℱ (fun ω s => -H ω s) hmn hpn hqn T
--         =ᵐ[P] fun ω => -stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFinsetSum`](https://prove2.me/theorems/3c65a1ac-837e-48a1-b323-dc87feeb6397).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stochasticIntegralBrownian_const_mul`](https://prove2.me/theorems/ac110cf4-8674-43ad-ab92-f7fde08971b6).
--
--   Next: [`stochasticIntegralBrownian_sub`](https://prove2.me/theorems/a954497d-231b-4ebc-910f-e11817f51410).
--
--   [Source excerpt, lines 48–58](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFinsetSum.lean#L48-L58) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFinsetSum.lean#L46-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFinsetSum`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFinsetSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFinsetSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg_readable {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmn : Measurable (Function.uncurry fun ω s => -H ω s))
    (hpn : Probability.ProgressivelyMeasurable ℱ fun ω s => -H ω s)
    (hqn : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖-H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => -H ω s) hmn hpn hqn T
      =ᵐ[P] fun ω => -stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω := by sorry
