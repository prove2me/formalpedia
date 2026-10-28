-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_sq_increment_readable
-- name    : LevyStochCalc.Brownian.Ito.memLp_two_sq_increment_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:16.621229+00:00
-- url     : https://prove2.me/theorems/bdf6946b-1242-4316-90ea-7306d70caa0e
-- title:
--   L² Membership of a Squared Itô Increment
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$, and let $H$ be measurable, progressively measurable, and jointly square-integrable on every positive finite horizon. Suppose $C\ge0$ and $|H(\omega,s)|\le C$ for all $\omega,s$. If $0\le a<b$, then
--
--   $$\omega\mapsto\bigl(F_b(\omega)-F_a(\omega)\bigr)^2\in L^2(P),$$
--
--   where $F_t=\mathrm{stochasticIntegralBrownian}(W,\mathcal F,H,t)$. Equivalently, the displayed squared increment has `MemLp` exponent $2$ under $P$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem memLp_two_sq_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       MemLp (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
--         - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) 2 P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoQuadVarSum`](https://prove2.me/theorems/1add907f-537c-4a62-9c27-fe90c9b4a510).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`lintegral_stochasticIntegralBrownian_sub_pow_four_le`](https://prove2.me/theorems/65902486-10fb-4581-8867-4b4a6cc14280).
--
--   Previous: [`compensator_sub_bounds`](https://prove2.me/theorems/5e8ee404-c1c1-469d-8d85-45ab11b64d10) · Next: [`integral_sq_quadVarIncrement_le`](https://prove2.me/theorems/bb94fb53-5983-4031-9e2b-578cca0d2b19).
--
--   [Source excerpt, lines 225–227](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L225-L227) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L223-L244 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoQuadVarSum`, declaration `LevyStochCalc.Brownian.Ito.memLp_two_sq_increment`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ hC0 hCH

theorem LevyStochCalc.Brownian.Ito.memLp_two_sq_increment_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) 2 P := by sorry
