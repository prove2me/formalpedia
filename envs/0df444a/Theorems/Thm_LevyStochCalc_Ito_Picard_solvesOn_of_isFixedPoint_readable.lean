-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_solvesOn_of_isFixedPoint_readable
-- name    : LevyStochCalc.Ito.Picard.solvesOn_of_isFixedPoint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:07.802977+00:00
-- url     : https://prove2.me/theorems/65f806f4-e0d8-4e52-9f10-b2384eb2ab37
-- title:
--   A Frozen Picard Fixed Point Solves On A Window
-- statement:
--   This is an auxiliary conversion theorem from a frozen fixed-point equation to `SolvesOn`. Let $W,N,\mathcal F$ and regular Lipschitz coefficients satisfy the stated hypotheses, let $x_0\in\mathbb R^n$, and let $T\geq0$. Suppose $Y:\mathbb R\to\Omega\to(\operatorname{Fin}(n)\to\mathbb R)$ is jointly measurable, progressively measurable, has finite Bielecki norm, and has finite $S^2$-type supremum integral on every positive interval. Assume that for every $t\in[0,T]$, $Y_t$ agrees almost surely coordinatewise with its frozen Picard step:
--
--   $$\forall t\in[0,T],\quad Y_t=\operatorname{picardStepOnRawStop}(Y,t)\quad P\text{-a.s.}$$
--
--   Then `SolvesOn W N ℱ ... x₀ Y T` holds. The result packages the required measurability and integrability witnesses and uses the equality before the horizon to obtain the standard jump-diffusion equation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem solvesOn_of_isFixedPoint
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → (Fin n → ℝ)}
--       (hYm : Measurable (Function.uncurry Y))
--       (hYa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
--       (hYb : bieleckiNorm (P := P) 0 T Y < ⊤)
--       (hYS : ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--       (hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
--         Y t ω i = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT x₀ t ω i) :
--       SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Ito/PicardIntegrandFrozen`](https://prove2.me/theorems/a8112e63-ece0-4e4f-915e-522b9de90238).
--
--   Supporting theorems: [`picardStep_rawStop_congr_ae`](https://prove2.me/theorems/5db0caec-c4f8-4145-9624-8dfa7e854eeb).
--
--   Previous: [`picardStep_rawStop_congr_ae`](https://prove2.me/theorems/5db0caec-c4f8-4145-9624-8dfa7e854eeb) · Next: [`exists_solvesOn`](https://prove2.me/theorems/cb1bf20c-3f06-408a-be53-4bceccae12cb).
--
--   [Source excerpt, lines 407–418](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardWindow.lean#L407-L418) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardWindow.lean#L406-L430 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardWindow`, declaration `LevyStochCalc.Ito.Picard.solvesOn_of_isFixedPoint`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

theorem LevyStochCalc.Ito.Picard.solvesOn_of_isFixedPoint_readable
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → (Fin n → ℝ)}
    (hYm : Measurable (Function.uncurry Y))
    (hYa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    (hYb : bieleckiNorm (P := P) 0 T Y < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
      Y t ω i = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT x₀ t ω i) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by sorry
