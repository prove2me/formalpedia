-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_solvesOn_globalPatch_readable
-- name    : LevyStochCalc.Ito.Picard.solvesOn_globalPatch_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:23.824448+00:00
-- url     : https://prove2.me/theorems/2037a307-1801-4e9b-8f73-f67d1076a421
-- title:
--   The Global Patch Solves On Every Finite Window
-- statement:
--   Let $W,N,\mathcal F$ and regular Lipschitz coefficients satisfy the stated Brownian, Poisson, and integrability hypotheses. Let $Y_k$ be a family of path maps, indexed by $k\in\mathbb N$, with each $Y_k$ jointly and progressively measurable and with finite $S^2$-type supremum integrals on positive intervals. Assume that, almost surely, `globalPatch Y` agrees with $Y_k$ on $[0,k+1]$, and that each $Y_k$ satisfies
--
--   $$\operatorname{SolvesOn}(Y_k,k+1).$$
--
--   Then for every $T\in\mathbb R$,
--
--   $$\operatorname{SolvesOn}(\operatorname{globalPatch}(Y),T).$$
--
--   The theorem formalizes compatibility of finite-window solutions under gluing and permits reuse of a consistent family of local solutions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem solvesOn_globalPatch
--       (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
--       {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
--       (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
--       (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
--       (hYa : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
--       (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
--         globalPatch Y t ω = Y k t ω)
--       (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
--       (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) (T : ℝ) :
--       SolvesOn W N ℱ hℱW hℱN coeffs x₀ (globalPatch Y) T
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083).
--
--   Definition modules: [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f), [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`picardStep_diffusion_congr_ae`](https://prove2.me/theorems/6c336559-f093-4ef9-8ae4-892731263519), [`picardStep_jump_congr_ae`](https://prove2.me/theorems/dbbc5d31-c9ed-480b-b61a-98ddb19cdde2), [`progressivelyMeasurable_globalPatch`](https://prove2.me/theorems/d7b4eeb7-145e-4369-9114-1296769d3100).
--
--   Previous: [`cadlag_globalPatch`](https://prove2.me/theorems/3d125985-be22-4ea3-8cfc-9c8457d42cde) · Next: [`exists_globalSolution`](https://prove2.me/theorems/90eec698-1731-47a5-9f64-89ce1ff7ee42).
--
--   [Source excerpt, lines 249–260](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardGlobal.lean#L249-L260) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardGlobal.lean#L248-L306 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardGlobal`, declaration `LevyStochCalc.Ito.Picard.solvesOn_globalPatch`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Ito.Picard.solvesOn_globalPatch_readable
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYa : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ (globalPatch Y) T := by sorry
