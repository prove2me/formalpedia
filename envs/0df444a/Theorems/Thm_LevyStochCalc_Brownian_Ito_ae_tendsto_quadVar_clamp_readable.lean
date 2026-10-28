-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_tendsto_quadVar_clamp_readable
-- name    : LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:41.582588+00:00
-- url     : https://prove2.me/theorems/16916452-8c4c-472a-be6e-b3b0e160f768
-- title:
--   Pathwise Convergence of Clamped Quadratic Variation
-- statement:
--   Let f″ be continuous and bounded by K₂ ≥ 0, let H be coordinatewise measurable with the stated finite `ENNReal` square-energy conditions, and let Y_i be measurable paths converging almost everywhere on [0,T] to X with i ≤ ns(i). Then for P-almost every ω and every p, q : Fin n,
--
--   $$\int_{(0,T]}\partial_{pq}^2f''(Y_i(s,\omega))\sum_k\operatorname{clampCoeff}(H,ns(i))_{p,k}(\omega,s)\operatorname{clampCoeff}(H,ns(i))_{q,k}(\omega,s)\,ds$$
--
--   converges to
--
--   $$\int_{(0,T]}\partial_{pq}^2f''(X(s,\omega))\sum_kH_{p,k}(\omega,s)H_{q,k}(\omega,s)\,ds.$$
--
--   This is the pathwise quadratic-variation convergence component of the clamped-coefficient approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_tendsto_quadVar_clamp
--       {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hf''c : Continuous f'')
--       {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
--       {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
--       {T : ℝ}
--       (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
--       (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
--       {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
--       (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
--         Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
--       ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
--           coordDeriv₂ f'' p q (Y i s ω)
--             * ∑ k : Fin d, clampCoeff H (ns i) p k ω s * clampCoeff H (ns i) q k ω s ∂volume)
--         Filter.atTop
--         (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
--           coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands`](https://prove2.me/theorems/93dff424-3aa2-4db6-a70a-d760c8275626).
--
--   Definition modules: [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Previous: [`ae_tendsto_drift_clamp`](https://prove2.me/theorems/0d88cd49-1116-49bb-b468-6962f08cda7d) · Next: [`tendsto_energy_coordDeriv_diff`](https://prove2.me/theorems/e842477b-9ddd-4040-94c5-e3ad7ba70732).
--
--   [Source excerpt, lines 102–119](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L102-L119) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L100-L159 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`, declaration `LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp_readable
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hf''c : Continuous f'')
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (Y i s ω)
          * ∑ k : Fin d, clampCoeff H (ns i) p k ω s * clampCoeff H (ns i) q k ω s ∂volume)
      Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) := by sorry
