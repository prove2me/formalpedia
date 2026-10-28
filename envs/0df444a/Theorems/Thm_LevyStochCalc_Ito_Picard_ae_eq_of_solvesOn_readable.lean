-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_ae_eq_of_solvesOn_readable
-- name    : LevyStochCalc.Ito.Picard.ae_eq_of_solvesOn_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:01.350993+00:00
-- url     : https://prove2.me/theorems/68acae9c-cef9-4b55-9b63-0571ce263cb6
-- title:
--   Almost-Sure Uniqueness of Window Solutions
-- statement:
--   This formalizes uniqueness on a finite time window for two solutions of the same jump-diffusion equation.
--
--   Let $P$ be a probability measure, $W$ a multidimensional Brownian motion, $N$ a Poisson random measure with sigma-finite intensity measure, and $\mathcal F$ filtrations for which the Brownian and Poisson compatibility assumptions hold. Let the coefficients be regular and Lipschitz with constant $L$. Let $X,Y:\mathbb R\to\Omega\to\mathbb R^n$ be jointly measurable, have finite $S^2$ energy on every positive window, and both solve the same equation with initial state $x_0$ on $[0,T]$, where $T>0$.
--
--   Then
--
--   $$\forall t\in[0,T],\quad \forall^{\mathrm{a.e.}}\,\omega\sim P,\ \forall i<n,\quad X(t,\omega,i)=Y(t,\omega,i).$$
--
--   This is an almost-sure, time-by-time uniqueness statement; it does not itself assert simultaneous equality of whole paths.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_eq_of_solvesOn
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       {X Y : ℝ → Ω → (Fin n → ℝ)}
--       (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
--       (hXS : ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--       (hYS : ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--       {T : ℝ} (hT : 0 < T)
--       (hX : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
--       (hY : SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T) :
--       ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n, X t ω i = Y t ω i
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3).
--
--   Supporting theorems: [`ae_eq_zero_of_bieleckiNorm_eq_zero`](https://prove2.me/theorems/03028af0-5e72-4f50-a46d-8baf738dd95f), [`bieleckiNorm_lt_top_of_supL2`](https://prove2.me/theorems/2df643b2-8d67-4af3-bd4c-c76523b1d9d8), [`bieleckiNorm_sub_lt_top_of_lt_top`](https://prove2.me/theorems/02064a85-b521-4d2a-aa86-6273c40d71ff), [`exists_bieleckiWeight_rate_lt_one`](https://prove2.me/theorems/2424b633-168d-49a1-be31-197cd8b56a43).
--
--   Previous: [`bieleckiNorm_sub_lt_top_of_lt_top`](https://prove2.me/theorems/02064a85-b521-4d2a-aa86-6273c40d71ff) · Next: [`picardStep_rawStop_congr_ae`](https://prove2.me/theorems/5db0caec-c4f8-4145-9624-8dfa7e854eeb).
--
--   [Source excerpt, lines 193–205](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardWindow.lean#L193-L205) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardWindow.lean#L191-L256 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardWindow`, declaration `LevyStochCalc.Ito.Picard.ae_eq_of_solvesOn`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
variable (x₀ : Fin n → ℝ)

theorem LevyStochCalc.Ito.Picard.ae_eq_of_solvesOn_readable
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hX : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
    (hY : SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n, X t ω i = Y t ω i := by sorry
