-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sub_sq_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_sub_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:06.584209+00:00
-- url     : https://prove2.me/theorems/943c5a51-ca07-4807-82e3-773eb2dc5277
-- title:
--   Second-Moment Bound for a Stochastic-Integral Increment
-- statement:
--   This is a technical moment estimate for increments of a scalar Itô integral.
--
--   Let $(\Omega,P)$ be a probability space, let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, and let $H:\Omega\times\mathbb R\to\mathbb R$ be measurable and progressively measurable. Assume that for every $T>0$ its time-space squared norm has finite $\mathrm{ENNReal}$ integral, that $C\ge 0$, and that $|H(\omega,s)|\le C$ for all $\omega,s$. For $0\le a<b$, write $M_t=\texttt{stochasticIntegralBrownian}(W,\mathcal F,H,t)$.
--
--   Then $M_b-M_a$ is square-integrable and
--   $$
--   \int (M_b-M_a)^2\,dP\le C^2(b-a).
--   $$
--
--   The result supplies the second-moment estimate used to derive first- and higher-moment bounds for stochastic-integral increments.
--
--   **Formalization Note** The hypotheses use an $\mathrm{ENNReal}$ finiteness condition for the integrated squared norm of $H$; the conclusion is an ordinary real integral and includes integrability explicitly.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sub_sq_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       MeasureTheory.Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
--           - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) P
--         ∧ ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
--             - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 ∂P
--           ≤ C ^ 2 * (b - a)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoIncrementMomentBounds`](https://prove2.me/theorems/c885777c-b44d-403b-b189-0d5182c90d15).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`lintegral_stochasticIntegralBrownian_sub_sq_le`](https://prove2.me/theorems/0e7c5bb8-1257-4ddd-a411-f3d6af20e053).
--
--   Previous: [`integral_sub_pow_four_le`](https://prove2.me/theorems/12ff2533-d8a3-4978-a4f3-a45469d7fa7c) · Next: [`integral_abs_sub_pow_three_le`](https://prove2.me/theorems/a7606041-e2f6-444b-9bd8-b9c435c0037c).
--
--   [Source excerpt, lines 443–448](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L443-L448) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean#L441-L481 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentBounds`, declaration `LevyStochCalc.Brownian.Ito.integral_sub_sq_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.integral_sub_sq_le_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) P
      ∧ ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 ∂P
        ≤ C ^ 2 * (b - a) := by sorry
