-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_coordDeriv_diff_readable
-- name    : LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:07.992306+00:00
-- url     : https://prove2.me/theorems/e842477b-9ddd-4040-94c5-e3ad7ba70732
-- title:
--   Energy Convergence of Perturbed Derivative Integrands
-- statement:
--   Let $f'$ be a continuous bounded derivative map with $\|f'(z)\|\le K_1$, where $K_1\ge0$. Let $G$ be measurable and have finite squared energy on $[0,T]$. If measurable vector fields $Y_i(s,\omega)$ converge to $X(s,\omega)$ almost everywhere on the window, then for each coordinate $p$,
--
--   $$
--   \int_\Omega\int_{[0,T]}
--   \left\|\bigl(\partial_p f'(Y_i)-\partial_p f'(X)\bigr)G\right\|^2
--   \,ds\,dP\longrightarrow0.
--   $$
--
--   The convergence is expressed as a filter limit to $0$ of `ENNReal` energy integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_energy_coordDeriv_diff
--       {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
--       {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
--       {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
--       (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
--       (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
--       (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
--       (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
--         Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
--       (p : Fin n) :
--       Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
--             ∂volume ∂P) Filter.atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands`](https://prove2.me/theorems/93dff424-3aa2-4db6-a70a-d760c8275626).
--
--   Definition modules: [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d).
--
--   Previous: [`ae_tendsto_quadVar_clamp`](https://prove2.me/theorems/16916452-8c4c-472a-be6e-b3b0e160f768) · Next: [`tendsto_energy_diffusionIntegrand_clamp`](https://prove2.me/theorems/9cee699e-7563-482a-af58-2791b1f7cffd).
--
--   [Source excerpt, lines 162–176](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L162-L176) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L161-L258 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`, declaration `LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

theorem LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff_readable
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by sorry
