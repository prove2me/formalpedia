-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_sub_stochasticIntegral_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:12.960682+00:00
-- url     : https://prove2.me/theorems/b9104289-b232-47cf-94d1-9015281546b4
-- title:
--   First Absolute Moment of a Scalar Itô Increment
-- statement:
--   This is a first-absolute-moment estimate for an increment of a scalar Itô integral.
--
--   Let $(\Omega,P)$ be a probability space, let $W$ have Brownian filtration $\mathcal F$, and let $H$ be measurable and progressively measurable. Assume the integrated squared norm of $H$ is finite on every positive time interval, $C\ge0$, and $|H(\omega,s)|\le C$ for all $\omega,s$. For $0\le u<v$, set $M_t=\texttt{stochasticIntegralBrownian}(W,\mathcal F,H,t)$.
--
--   Then $M_v-M_u$ is integrable in absolute value and
--   $$
--   \int |M_v-M_u|\,dP\le C\sqrt{v-u}.
--   $$
--
--   The estimate is the scalar martingale-increment bound used in subsequent vector and Itô-process estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_sub_stochasticIntegral_le {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
--       MeasureTheory.Integrable (fun ω : Ω =>
--           |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
--             - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) P
--         ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
--               - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| ∂P
--             ≤ C * Real.sqrt (v - u)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoProcess`](https://prove2.me/theorems/0e852a7e-a66b-4b2e-af71-2e5817bdbfa8).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integral_sub_sq_le`](https://prove2.me/theorems/943c5a51-ca07-4807-82e3-773eb2dc5277), [`integral_abs_le_sqrt_of_integral_sq_le`](https://prove2.me/theorems/bfdc1797-b9af-45f2-9493-fd8068fd1149).
--
--   Previous: [`integrable_abs_drift_pow`](https://prove2.me/theorems/a6288035-95df-498a-8432-a20089aba59f).
--
--   [Source excerpt, lines 263–269](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoProcess.lean#L263-L269) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoProcess.lean#L261-L286 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ hC0 hCH

theorem LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le_readable {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) P
      ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| ∂P
          ≤ C * Real.sqrt (v - u) := by sorry
