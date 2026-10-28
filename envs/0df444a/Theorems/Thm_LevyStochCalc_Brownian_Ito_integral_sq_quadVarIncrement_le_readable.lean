-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_quadVarIncrement_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:49.641044+00:00
-- url     : https://prove2.me/theorems/bb94fb53-5983-4031-9e2b-578cca0d2b19
-- title:
--   Second-Moment Bound for Compensated Square Increments
-- statement:
--   Let $H$ satisfy the measurability, progressive-measurability, joint square-integrability, and uniform bound assumptions above, with $C\ge0$. For $0\le a<b$, the compensated square increment has an integrable square and
--
--   $$\int \mathrm{quadVarIncrement}_{a,b}(\omega)^2\,dP(\omega)
--   \le \bigl(2(6+\gamma_4)+2\bigr)C^4(b-a)^2,$$
--
--   where $\gamma_4$ is the Lean constant `gaussianFourthMoment`. The declaration gives the inequality for the second moment; its integrability follows from the same hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_quadVarIncrement_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       ∫ ω, (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
--         ≤ (2 * (6 + gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoQuadVarSum`](https://prove2.me/theorems/1add907f-537c-4a62-9c27-fe90c9b4a510).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`compensator_sub_bounds`](https://prove2.me/theorems/5e8ee404-c1c1-469d-8d85-45ab11b64d10), [`lintegral_stochasticIntegralBrownian_sub_pow_four_le`](https://prove2.me/theorems/65902486-10fb-4581-8867-4b4a6cc14280), [`memLp_two_sq_increment`](https://prove2.me/theorems/bdf6946b-1242-4316-90ea-7306d70caa0e).
--
--   Previous: [`memLp_two_sq_increment`](https://prove2.me/theorems/bdf6946b-1242-4316-90ea-7306d70caa0e) · Next: [`exists_continuous_modification_stochasticIntegralBrownian`](https://prove2.me/theorems/e5f854d8-aecd-421d-a4fc-24ba2b3c40e0).
--
--   [Source excerpt, lines 268–270](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L268-L270) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L266-L372 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoQuadVarSum`, declaration `LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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

theorem LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ (2 * (6 + gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by sorry
