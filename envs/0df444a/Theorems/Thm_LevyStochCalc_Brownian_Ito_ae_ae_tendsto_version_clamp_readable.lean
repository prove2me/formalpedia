-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_ae_tendsto_version_clamp_readable
-- name    : LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:50.873981+00:00
-- url     : https://prove2.me/theorems/4b4b00a1-8893-4a14-9b71-7455375e4cb1
-- title:
--   Almost-Everywhere Window Convergence of Clamped Versions
-- statement:
--   Under the stated probability-space, Brownian-motion, measurability, progressive measurability, finite-energy, and Itô-version assumptions, let X be the original version and Xj the version with coefficients clamped at levels j. Let ns : ℕ → ℕ satisfy
--
--   $$\operatorname{clampMesh}(P,H,b,T,ns(i))<\left(2^{-1}\right)^i$$
--
--   for every i. Then, for P-almost every ω and Lebesgue-almost every s in [0,T],
--
--   $$X_{ns(i)}(s,\omega)\to X(s,\omega).$$
--
--   The two a.e. qualifiers are explicit: the outer one is with respect to P and the inner one with respect to restricted Lebesgue measure on the time window. This provides pathwise window convergence along a sufficiently fast subsequence of truncation levels.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_ae_tendsto_version_clamp
--       {H : Fin n → Fin d → Ω → ℝ → ℝ}
--       {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
--       {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
--       {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
--       {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
--       {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
--       (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X : ℝ → Ω → Fin n → ℝ} {Xj : ℕ → ℝ → Ω → Fin n → ℝ}
--       (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
--       (hXj : ∀ j : ℕ, IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
--         (fun p k => measurable_clampCoeff hm j p k)
--         (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
--         (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
--         X₀ (clampDrift b j) (Xj j))
--       {T : ℝ} {ns : ℕ → ℕ}
--       (hns : ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i) :
--       ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
--         Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`lintegral_window_sq_norm_version_clamp_sub_le`](https://prove2.me/theorems/c96d8a38-efbf-4a2e-a1e2-fc59d1d0efa6), [`tendsto_of_tendsto_sq_enorm`](https://prove2.me/theorems/98542836-cccb-4492-8290-6e6d19d114a0).
--
--   Previous: [`exists_seq_ae_tendsto_of_tendsto_lintegral`](https://prove2.me/theorems/3562f88f-3c78-4ff5-ad93-01edc45ad90f) · Next: [`ae_tendsto_version_clamp_at`](https://prove2.me/theorems/749d431d-d8f1-44b6-ba64-5d3e7974a377).
--
--   [Source excerpt, lines 430–450](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L430-L450) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L428-L477 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`, declaration `LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ')

theorem LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp_readable
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Xj : ℕ → ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : ∀ j : ℕ, IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) (Xj j))
    {T : ℝ} {ns : ℕ → ℕ}
    (hns : ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) := by sorry
