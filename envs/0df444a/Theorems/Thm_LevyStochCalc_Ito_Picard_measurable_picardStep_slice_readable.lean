-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_measurable_picardStep_slice_readable
-- name    : LevyStochCalc.Ito.Picard.measurable_picardStep_slice_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:48.666989+00:00
-- url     : https://prove2.me/theorems/1e31c07e-8da8-413f-8f5b-0db985513884
-- title:
--   Slice Measurability of the Picard Step
-- statement:
--   This proves measurability in the sample point of the Picard step at each fixed time and coordinate.
--
--   Let $P$ be a probability measure, $W$ a multidimensional Brownian motion, $N$ a Poisson random measure with sigma-finite intensity, and $\mathcal F$ compatible filtrations. Let $X$ be a state process and $x_0$ an initial state. Assume the diffusion, jump, and drift coefficients are respectively measurable, progressively measurable where required, and have the stated finite squared-energy bounds on every positive window.
--
--   For every $t\in\mathbb R$ and $i<n$,
--
--   $$\omega\mapsto\operatorname{picardStep}(t,\omega,i)$$
--
--   is measurable. This is slice measurability only; the statement does not assert joint measurability in $(t,\omega)$.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       (h_γ_meas : ∀ i : Fin n,
--         Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
--       (h_γ_progMeas : ∀ i : Fin n,
--         Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
--       (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
--           (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
--       (h_μ_meas : ∀ i : Fin n,
--         Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
--       (t : ℝ) (i : Fin n) :
--       Measurable fun ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
--         h_γ_meas h_γ_progMeas h_γ_sq t ω i
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardOutputStepDiff`](https://prove2.me/theorems/533f48a7-fd20-44bc-a9bd-d65960049bdb).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Ito/PicardStepMap`](https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   [Source excerpt, lines 145–156](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardOutputStepDiff.lean#L145-L156) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardOutputStepDiff.lean#L126-L168 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardOutputStepDiff`, declaration `LevyStochCalc.Ito.Picard.measurable_picardStep_slice`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardOutputStepDiff

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardOutputStepDiff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

theorem LevyStochCalc.Ito.Picard.measurable_picardStep_slice_readable
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (t : ℝ) (i : Fin n) :
    Measurable fun ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq t ω i := by sorry
