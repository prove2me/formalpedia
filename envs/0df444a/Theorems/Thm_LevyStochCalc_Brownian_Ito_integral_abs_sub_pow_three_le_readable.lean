-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_sub_pow_three_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_sub_pow_three_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:18.369711+00:00
-- url     : https://prove2.me/theorems/a7606041-e2f6-444b-9bd8-b9c435c0037c
-- title:
--   Third Absolute Moment of a Scalar Itô-Integral Increment
-- statement:
--   This formalizes a third-moment estimate for a scalar Itô-integral increment.
--
--   Let $P$ be a probability measure, let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, and let $H:\Omega\times\mathbb R\to\mathbb R$ be measurable and progressively measurable. Assume its squared extended integral on every $[0,T]$, $T>0$, is finite. Let $C\ge0$ and suppose $|H(\omega,s)|\le C$. For $0\le a<b$, define $c=\texttt{gaussianFourthMoment}$. Then the increment is cubically integrable and
--   $$
--   \int_\Omega\left|\int_a^b H_s\,dW_s\right|^3dP
--   \le
--   \frac{C^2+(6+c)C^4}{2}\,(b-a)\sqrt{b-a}.
--   $$
--
--   This is the scalar third absolute-moment input for vector martingale and Itô-process estimates.
--
--   **Formalization Note** The declaration also asserts integrability of the cubed increment. `gaussianFourthMoment` is the Lean constant used for the Gaussian fourth moment.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_sub_pow_three_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       MeasureTheory.Integrable (fun ω => |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
--           - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P
--         ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
--             - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
--           ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
--             * ((b - a) * Real.sqrt (b - a))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoIncrementMomentBounds`](https://prove2.me/theorems/c885777c-b44d-403b-b189-0d5182c90d15).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integral_sub_pow_four_le`](https://prove2.me/theorems/12ff2533-d8a3-4978-a4f3-a45469d7fa7c), [`integral_sub_sq_le`](https://prove2.me/theorems/943c5a51-ca07-4807-82e3-773eb2dc5277).
--
--   Previous: [`integral_sub_sq_le`](https://prove2.me/theorems/943c5a51-ca07-4807-82e3-773eb2dc5277).
--
--   [Source excerpt, lines 486–492](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L486-L492) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L483-L547 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentBounds`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_sub_pow_three_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ hC0 hCH

theorem LevyStochCalc.Brownian.Ito.integral_abs_sub_pow_three_le_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P
      ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
        ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * ((b - a) * Real.sqrt (b - a)) := by sorry
