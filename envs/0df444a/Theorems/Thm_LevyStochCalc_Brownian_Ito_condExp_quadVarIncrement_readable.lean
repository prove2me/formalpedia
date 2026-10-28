-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_quadVarIncrement_readable
-- name    : LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:53.787209+00:00
-- url     : https://prove2.me/theorems/cb7ab2d0-c60c-4b01-a336-abec1be3188b
-- title:
--   Conditional Centering of Compensated Square Increments
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, and let $H$ be measurable, progressively measurable, and square-integrable on every finite positive horizon in the stated joint sense. For $0\le a\le b$, define `quadVarIncrement` as the squared Itô-integral increment minus the compensator increment. Then
--
--   $$\mathbb E\!\left[\mathrm{quadVarIncrement}_{a,b}\mid\mathcal F.\mathrm{rightCont}_a\right]=0\quad\text{a.e. }P.$$
--
--   Thus the compensated square increment is conditionally centered at its left endpoint.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem condExp_quadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
--       P[quadVarIncrement W ℱ hℱ H hm hp hq a b | ℱ.rightCont a] =ᵐ[P] 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoQuadVarSum`](https://prove2.me/theorems/1add907f-537c-4a62-9c27-fe90c9b4a510).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`martingale_rightCont_quadVar_stochasticIntegralBrownian`](https://prove2.me/theorems/0df2e8f2-7807-4907-a708-b5a34a8e6b9e).
--
--   Next: [`compensator_sub_bounds`](https://prove2.me/theorems/5e8ee404-c1c1-469d-8d85-45ab11b64d10).
--
--   [Source excerpt, lines 58–59](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L58-L59) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L56-L138 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoQuadVarSum`, declaration `LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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

theorem LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P[quadVarIncrement W ℱ hℱ H hm hp hq a b | ℱ.rightCont a] =ᵐ[P] 0 := by sorry
