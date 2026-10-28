-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_diffusionIntegrand_clamp_readable
-- name    : LevyStochCalc.Brownian.Ito.tendsto_energy_diffusionIntegrand_clamp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:34.556708+00:00
-- url     : https://prove2.me/theorems/9cee699e-7563-482a-af58-2791b1f7cffd
-- title:
--   Energy Convergence of Clamped Diffusion Integrands
-- statement:
--   Let $f'$ be continuous with bounded norm $K_1$, let $H_{pk}$ be measurable and square-integrable on $[0,T]$, and let $Y_i\to X$ almost everywhere on the window. For a subsequence map $n_i$ satisfying $i\le n_i$, the clamped diffusion integrands converge in energy: for every coordinate $p$ and Brownian index $k$,
--
--   $$
--   \int_\Omega\int_{[0,T]}
--   \left\|\partial_p f'(Y_i)\,\operatorname{clampCoeff}(H,n_i)_{pk}
--   -\partial_p f'(X)H_{pk}\right\|^2
--   \,ds\,dP\longrightarrow0.
--   $$
--
--   The conclusion is an `ENNReal` limit and includes the stated measurability and integrability assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_energy_diffusionIntegrand_clamp
--       {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
--       {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
--       {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
--       {T : ℝ}
--       (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
--       (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
--       (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
--       {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
--       (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
--         Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
--       (p : Fin n) (k : Fin d) :
--       Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s
--             - coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--         Filter.atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands`](https://prove2.me/theorems/93dff424-3aa2-4db6-a70a-d760c8275626).
--
--   Definition modules: [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Supporting theorems: [`tendsto_energy_clampAt_sub`](https://prove2.me/theorems/554d2154-b037-4ba4-9d29-93ade89b3950), [`tendsto_energy_coordDeriv_diff`](https://prove2.me/theorems/e842477b-9ddd-4040-94c5-e3ad7ba70732).
--
--   Previous: [`tendsto_energy_coordDeriv_diff`](https://prove2.me/theorems/e842477b-9ddd-4040-94c5-e3ad7ba70732).
--
--   [Source excerpt, lines 287–304](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L287-L304) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L286-L396 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`, declaration `LevyStochCalc.Brownian.Ito.tendsto_energy_diffusionIntegrand_clamp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.tendsto_energy_diffusionIntegrand_clamp_readable
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) (k : Fin d) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s
          - coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) := by sorry
