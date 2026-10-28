-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_ae_zero_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:10.55929+00:00
-- url     : https://prove2.me/theorems/57111c52-f9fc-4a29-b5e6-79796fbc45a3
-- title:
--   Almost-Sure Vanishing of the Zero Itô Integral
-- statement:
--   This statement shows that the Brownian Itô integral of the zero integrand vanishes almost surely. Let $(Ω,P)$ be a probability space, let $W$ be a Brownian motion, and let $ℱ$ be a Brownian filtration. Assume that the zero process is measurable and progressively measurable and that its squared `ENNReal` energy is finite on every interval $[0,T]$ with $T>0$.
--
--   For every $t∈ℝ$,
--
--   $$\texttt{stochasticIntegralBrownian}(0,t)=0\quad P\text{-almost everywhere}.$$
--
--   The conclusion holds for arbitrary real times, including nonpositive times. This is the zero element property needed for the additive and finite-sum algebra of the integral.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_ae_zero
--       (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)))
--       (hp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ))
--       (hq : ∀ T, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
--         (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
--       stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t =ᵐ[P] 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoZero`](https://prove2.me/theorems/77654a98-9480-46ac-8fe1-93718b5d7f8a).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   [Source excerpt, lines 50–55](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoZero.lean#L50-L55) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoZero.lean#L48-L71 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoZero`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoZero

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoZero.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_readable
    (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)))
    (hp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ))
    (hq : ∀ T, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t =ᵐ[P] 0 := by sorry
