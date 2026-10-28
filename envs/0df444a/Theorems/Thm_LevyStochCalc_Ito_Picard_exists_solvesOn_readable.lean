-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_exists_solvesOn_readable
-- name    : LevyStochCalc.Ito.Picard.exists_solvesOn_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:20.702525+00:00
-- url     : https://prove2.me/theorems/cb1bf20c-3f06-408a-be53-4bceccae12cb
-- title:
--   Existence Of A Càdlàg Solution On A Finite Window
-- statement:
--   This is a finite-window existence theorem. Let $(\Omega,P)$ be a probability space carrying a $d$-dimensional Brownian motion $W$ and a Poisson random measure $N$ with mark measure $\nu$, and let $\mathcal F$ be a right-continuous filtration making them Brownian and Poisson. Assume the filtration is ordered at nonpositive times, $P$-null measurable sets are measurable at time $0$, and the jump-diffusion coefficients are regular and Lipschitz with some constant $L$. For every initial state $x_0\in\mathbb R^n$ and every $T>0$, there exists a path map $Y:\mathbb R\times\Omega\to\mathbb R^n$ such that
--
--   1. $Y$ is jointly measurable and each coordinate is progressively measurable;
--   2. for $P$-almost every $\omega$, $t\mapsto Y_t(\omega)$ is right-continuous with a left limit at every real time, coordinatewise on the left;
--   3. for every $T'>0$,
--   $$\int_\Omega\sup_{t\in[0,T']}\sum_{i=1}^n\|Y_t(\omega)_i\|_+^2\,dP<\infty;$$
--   4. `SolvesOn W N ℱ ... x₀ Y T` holds.
--
--   Thus a càdlàg, progressively measurable solution exists on every positive finite window.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_solvesOn [ℱ.IsRightContinuous]
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T) :
--       ∃ Y : ℝ → Ω → (Fin n → ℝ),
--         Measurable (Function.uncurry Y)
--           ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
--           ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
--               Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
--                 ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
--                     Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
--           ∧ (∀ T' : ℝ, 0 < T' →
--               ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--           ∧ SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`exists_bieleckiWeight_rate_lt_one`](https://prove2.me/theorems/2424b633-168d-49a1-be31-197cd8b56a43), [`lintegral_sq_iSup_picardSelfMapRaw_lt_top`](https://prove2.me/theorems/41b19c73-2054-4724-85c9-087eb1b0c354), [`picardSelfMapRaw_isFixedPoint`](https://prove2.me/theorems/8d60ac0b-9ec8-46b3-ab34-28751499333d), [`solvesOn_of_isFixedPoint`](https://prove2.me/theorems/65f806f4-e0d8-4e52-9f10-b2384eb2ab37).
--
--   Previous: [`solvesOn_of_isFixedPoint`](https://prove2.me/theorems/65f806f4-e0d8-4e52-9f10-b2384eb2ab37).
--
--   [Source excerpt, lines 434–449](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardWindow.lean#L434-L449) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardWindow.lean#L432-L468 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardWindow`, declaration `LevyStochCalc.Ito.Picard.exists_solvesOn`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
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

theorem LevyStochCalc.Ito.Picard.exists_solvesOn_readable [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ Y : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry Y)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by sorry
