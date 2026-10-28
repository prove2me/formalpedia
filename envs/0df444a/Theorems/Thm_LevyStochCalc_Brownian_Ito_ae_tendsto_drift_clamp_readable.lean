-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_tendsto_drift_clamp_readable
-- name    : LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:48.497264+00:00
-- url     : https://prove2.me/theorems/0d88cd49-1116-49bb-b468-6962f08cda7d
-- title:
--   Pathwise Convergence of Clamped Drift Integrals
-- statement:
--   Let f′ be continuous on Fin n → ℝ with ‖f′(z)‖ ≤ K₁, let b be coordinatewise measurable with finite `ENNReal` square energy on [0,T], and let Y_i be measurable approximating paths. If i ≤ ns(i) and, for P-almost every ω and almost every s in [0,T], Y_i(s,ω) → X(s,ω), then for P-almost every ω and every p : Fin n,
--
--   $$\int_{(0,T]}\partial_p f'(Y_i(s,\omega))\,\operatorname{clampDrift}(b,ns(i),p,\omega,s)\,ds\to\int_{(0,T]}\partial_p f'(X(s,\omega))b_p(\omega,s)\,ds.$$
--
--   The statement does not require a probability-measure instance in Lean; it uses the displayed measurability and energy assumptions directly.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_tendsto_drift_clamp
--       {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
--       {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
--       {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
--       {T : ℝ}
--       (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
--       (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
--       {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
--       (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
--         Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
--       ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
--           coordDeriv f' p (Y i s ω) * clampDrift b (ns i) p ω s ∂volume) Filter.atTop
--         (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * b p ω s ∂volume))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands`](https://prove2.me/theorems/93dff424-3aa2-4db6-a70a-d760c8275626).
--
--   Definition modules: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb), [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d).
--
--   Next: [`ae_tendsto_quadVar_clamp`](https://prove2.me/theorems/16916452-8c4c-472a-be6e-b3b0e160f768).
--
--   [Source excerpt, lines 57–71](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L57-L71) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean#L55-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`, declaration `LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp_readable
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {T : ℝ}
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (Y i s ω) * clampDrift b (ns i) p ω s ∂volume) Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * b p ω s ∂volume)) := by sorry
