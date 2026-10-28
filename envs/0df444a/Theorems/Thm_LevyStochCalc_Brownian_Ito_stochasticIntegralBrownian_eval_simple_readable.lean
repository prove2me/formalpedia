-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_eval_simple_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:47.469321+00:00
-- url     : https://prove2.me/theorems/cae7fbf2-3586-459d-92c8-a9b6a264de7f
-- title:
--   Itô Integral Equals Elementary Integral for Simple Integrands
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration, let $G$ be a simple predictable integrand, and assume all coefficients of $G$ are strongly measurable at their preceding partition times. Suppose the evaluation of $G$ is jointly measurable, progressively measurable, and has finite squared `ENNReal` energy on every positive time interval. Then, for every $t≥0$,
--
--   $$\texttt{stochasticIntegralBrownian}(G,t)=\texttt{simpleIntegral}(W,G,t)\quad P\text{-almost everywhere}.$$
--
--   The conclusion is equality of random variables modulo $P$-null sets. This identifies the abstract `L²` Itô integral with the elementary finite-sum construction on simple predictable inputs.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_eval_simple {t : ℝ} (ht : 0 ≤ t) :
--       stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
--         =ᵐ[P] simpleIntegral W G t
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand`](https://prove2.me/theorems/09c55224-b261-4948-9982-f2ec68361149).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`simpleIntegral_diff_isometry_of_adapted`](https://prove2.me/theorems/2683d1bc-8d01-4352-8fe2-981705a37ca4).
--
--   Previous: [`simpleIntegral_diff_isometry_of_adapted`](https://prove2.me/theorems/2683d1bc-8d01-4352-8fe2-981705a37ca4).
--
--   [Source excerpt, lines 238–240](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean#L238-L240) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean#L236-L335 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ h_adapt

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple_readable {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
      =ᵐ[P] simpleIntegral W G t := by sorry
