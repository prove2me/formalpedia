-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_exists_globalSolution_readable
-- name    : LevyStochCalc.Ito.Picard.exists_globalSolution_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:23.968991+00:00
-- url     : https://prove2.me/theorems/90eec698-1731-47a5-9f64-89ce1ff7ee42
-- title:
--   Existence Of A Global Jump-Diffusion Solution
-- statement:
--   This is a global existence theorem. Let $(\Omega,P)$ carry a multidimensional Brownian motion $W$ and Poisson random measure $N$, and let $\mathcal F$ be right-continuous, with the stated ordering at nonpositive times and null-set measurability condition. Assume the jump-diffusion coefficients are regular and globally Lipschitz with constant $L$. For every initial state $x_0\in\mathbb R^n$, there exists $X:\mathbb R\to\Omega\to\mathbb R^n$ such that
--
--   1. $X$ is jointly measurable and progressively measurable coordinatewise;
--   2. $X_0=x_0$ almost surely;
--   3. almost surely, for every $t\geq0$, $X$ is right-continuous at $t$ and every coordinate has a left limit at $t$;
--   4. for every $T'>0$,
--   $$\int_\Omega\sup_{t\in[0,T']}\sum_i\|X_t(\omega)_i\|_+^2\,dP<\infty;$$
--   5. for every $T\in\mathbb R$, `SolvesOn W N ℱ ... x₀ X T` holds.
--
--   The conclusion is existence on all finite windows, not a separate assertion of a single global norm over $[0,\infty)$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_globalSolution [ℱ.IsRightContinuous]
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) :
--       ∃ X : ℝ → Ω → (Fin n → ℝ),
--         Measurable (Function.uncurry X)
--           ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
--           ∧ (∀ᵐ ω ∂P, X 0 ω = x₀)
--           ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
--               Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
--                 ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
--                     Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
--           ∧ (∀ T' : ℝ, 0 < T' →
--               ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--           ∧ (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`ae_all_windows_agree`](https://prove2.me/theorems/28b35a3b-dd08-4022-854c-84cd03274ea9), [`cadlag_globalPatch`](https://prove2.me/theorems/3d125985-be22-4ea3-8cfc-9c8457d42cde), [`exists_solvesOn`](https://prove2.me/theorems/cb1bf20c-3f06-408a-be53-4bceccae12cb), [`progressivelyMeasurable_globalPatch`](https://prove2.me/theorems/d7b4eeb7-145e-4369-9114-1296769d3100), [`solvesOn_globalPatch`](https://prove2.me/theorems/2037a307-1801-4e9b-8f73-f67d1076a421).
--
--   Previous: [`solvesOn_globalPatch`](https://prove2.me/theorems/2037a307-1801-4e9b-8f73-f67d1076a421).
--
--   [Source excerpt, lines 321–337](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardGlobal.lean#L321-L337) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardGlobal.lean#L318-L362 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardGlobal`, declaration `LevyStochCalc.Ito.Picard.exists_globalSolution`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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

theorem LevyStochCalc.Ito.Picard.exists_globalSolution_readable [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) :
    ∃ X : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry X)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
        ∧ (∀ᵐ ω ∂P, X 0 ω = x₀)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
            Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) := by sorry
