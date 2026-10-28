-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_ae_all_windows_agree_readable
-- name    : LevyStochCalc.Ito.Picard.ae_all_windows_agree_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:30.008442+00:00
-- url     : https://prove2.me/theorems/28b35a3b-dd08-4022-854c-84cd03274ea9
-- title:
--   Almost-Sure Agreement of Nested Window Solutions
-- statement:
--   This promotes uniqueness on overlapping windows to simultaneous agreement of a family of window solutions.
--
--   Let $Y_k:\mathbb R\to\Omega\to\mathbb R^n$ for $k\in\mathbb N$ be jointly measurable, right-continuous almost surely, and have finite $S^2$ energy on every positive window. Assume every $Y_k$ solves the same regular Lipschitz jump-diffusion equation with initial state $x_0$ on $[0,k+1]$.
--
--   Then, almost surely, for every pair $p=(p_1,p_2)\in\mathbb N\times\mathbb N$ and every
--   $t\in[0,\min(p_1+1,p_2+1)]$,
--
--   $$Y_{p_1}(t,\omega)=Y_{p_2}(t,\omega).$$
--
--   This is the consistency statement needed to glue finite-window solutions into a global process.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_all_windows_agree
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
--       (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
--       (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
--         Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)))
--       (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--       (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) :
--       ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)),
--         Y p.1 t ω = Y p.2 t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3).
--
--   Supporting theorems: [`ae_all_eq_of_rightCont`](https://prove2.me/theorems/439cca99-ccce-4335-8a27-57cecb8617ae), [`ae_eq_of_solvesOn`](https://prove2.me/theorems/68acae9c-cef9-4b55-9b63-0571ce263cb6).
--
--   Previous: [`progressivelyMeasurable_globalPatch`](https://prove2.me/theorems/d7b4eeb7-145e-4369-9114-1296769d3100) · Next: [`cadlag_globalPatch`](https://prove2.me/theorems/3d125985-be22-4ea3-8cfc-9c8457d42cde).
--
--   [Source excerpt, lines 149–160](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardGlobal.lean#L149-L160) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardGlobal.lean#L148-L171 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardGlobal`, declaration `LevyStochCalc.Ito.Picard.ae_all_windows_agree`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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

theorem LevyStochCalc.Ito.Picard.ae_all_windows_agree_readable
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)))
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)),
      Y p.1 t ω = Y p.2 t ω := by sorry
