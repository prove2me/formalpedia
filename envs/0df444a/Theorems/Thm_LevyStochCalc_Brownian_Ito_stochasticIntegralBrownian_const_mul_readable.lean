-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_const_mul_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_const_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:47.661001+00:00
-- url     : https://prove2.me/theorems/ac110cf4-8674-43ad-ab92-f7fde08971b6
-- title:
--   Scalar Homogeneity of the Brownian Itô Integral
-- statement:
--   This statement establishes homogeneity of the Brownian Itô integral. Let $(Ω,P)$ be a probability space, let $W$ be a Brownian motion, and let $ℱ$ be a Brownian filtration. Let $H:Ω×ℝ→ℝ$ be jointly measurable and progressively measurable, with finite squared `ENNReal` energy on every $[0,T]$ for $T>0$. Fix $c∈ℝ$, and assume the scaled process $cH$ is jointly measurable, progressively measurable, and has finite squared energy on every positive time interval.
--
--   For every $T>0$,
--
--   $$\texttt{stochasticIntegralBrownian}(cH,T)=c\,\texttt{stochasticIntegralBrownian}(H,T)\quad P\text{-almost everywhere}.$$
--
--   The statement is pointwise in the scalar $c$ and time $T$, with all admissibility hypotheses for both integrands explicit. It complements additivity to provide linearity of the integral.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_const_mul {H : Ω → ℝ → ℝ}
--       (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (c : ℝ)
--       (hmc : Measurable (Function.uncurry fun ω s => c * H ω s))
--       (hpc : Probability.ProgressivelyMeasurable ℱ fun ω s => c * H ω s)
--       (hqc : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {T : ℝ} (hT : 0 < T) :
--       stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T
--         =ᵐ[P] fun ω => c * stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`ae_eq_const_mul_of_sq_distances`](https://prove2.me/theorems/bfc53c08-9b3b-4e24-881f-cb00e6aeeb58), [`lintegral_energy_const_mul`](https://prove2.me/theorems/ce857bc0-8f4c-4f64-b3bd-5184a06ec375).
--
--   Previous: [`ae_eq_const_mul_of_sq_distances`](https://prove2.me/theorems/bfc53c08-9b3b-4e24-881f-cb00e6aeeb58).
--
--   [Source excerpt, lines 346–357](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean#L346-L357) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLinear.lean#L344-L373 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLinear`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_const_mul`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_const_mul_readable {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (c : ℝ)
    (hmc : Measurable (Function.uncurry fun ω s => c * H ω s))
    (hpc : Probability.ProgressivelyMeasurable ℱ fun ω s => c * H ω s)
    (hqc : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T
      =ᵐ[P] fun ω => c * stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω := by sorry
