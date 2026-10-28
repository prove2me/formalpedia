-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_iSup_sq_norm_clamp_version_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:29.029995+00:00
-- url     : https://prove2.me/theorems/504b07f4-fd56-41ea-9704-d91515922d85
-- title:
--   Window Bound for Differences of Clamped Itô Versions
-- statement:
--   This bounds the window supremum of the difference between two clamped vector Itô versions.
--
--   Let $P$ be a probability measure, $W$ a $d$-dimensional Brownian motion, and $\mathcal F$ a filtration satisfying the stated Brownian-coordinate assumptions. Let $H$ and $b$ be measurable, progressively measurable coefficient and drift families with finite squared energy on every positive window. For clamping levels $j,j'\in\mathbb N$, let $X_j$ and $X_{j'}$ be vector Itô versions driven by the clamped coefficients and drifts, with common initial value.
--
--   For every $T>0$,
--
--   $$\int_\Omega\sup_{0\le t\le T}\|X_{j'}(t)-X_j(t)\|^2\,dP\le 32\,n^2\bigl(\operatorname{clampMesh}(P,H,b,T,j)+\operatorname{clampMesh}(P,H,b,T,j')\bigr).$$
--
--   The right-hand side is an `ENNReal` quantity. The result is a technical estimate used to control convergence of clamped versions on bounded time windows.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_iSup_sq_norm_clamp_version_sub_le
--       {H : Fin n → Fin d → Ω → ℝ → ℝ}
--       {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
--       {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
--       {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ}
--       (hbm : ∀ p, Measurable (Function.uncurry (b p)))
--       {j j' : ℕ} {Xj Xj' : ℝ → Ω → Fin n → ℝ}
--       (hXj : IsVectorItoVersion W ℱ hcoord (clampCoeff H j)
--         (fun p k => measurable_clampCoeff hm j p k)
--         (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
--         (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
--         X₀ (clampDrift b j) Xj)
--       (hXj' : IsVectorItoVersion W ℱ hcoord (clampCoeff H j')
--         (fun p k => measurable_clampCoeff hm j' p k)
--         (fun p k => progressivelyMeasurable_clampCoeff hpg j' p k)
--         (fun p k T' hT' => energy_clampCoeff_lt_top j' p k T' hT')
--         X₀ (clampDrift b j') Xj')
--       {T : ℝ} (hT : 0 < T) :
--       ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Xj' (t : ℝ) ω - Xj (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
--         ≤ 32 * (n : ℝ≥0∞) ^ 2 * (clampMesh P H b T j + clampMesh P H b T j')
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionUnbounded`](https://prove2.me/theorems/283f8eec-9617-48b4-836e-d610c16dd968).
--
--   Definition modules: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`lintegral_energy_sub_le`](https://prove2.me/theorems/b2a75191-454e-466b-aa72-6635b7bb48fd), [`lintegral_iSup_sq_norm_version_sub_le`](https://prove2.me/theorems/3d71b361-cb18-4a6b-a812-4786fccd9817).
--
--   [Source excerpt, lines 41–60](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionUnbounded.lean#L41-L60) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionUnbounded.lean#L38-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionUnbounded`, declaration `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionUnbounded

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionUnbounded.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
include hcoord

theorem LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le_readable
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
    {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {j j' : ℕ} {Xj Xj' : ℝ → Ω → Fin n → ℝ}
    (hXj : IsVectorItoVersion W ℱ hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) Xj)
    (hXj' : IsVectorItoVersion W ℱ hcoord (clampCoeff H j')
      (fun p k => measurable_clampCoeff hm j' p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j' p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j' p k T' hT')
      X₀ (clampDrift b j') Xj')
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Xj' (t : ℝ) ω - Xj (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 32 * (n : ℝ≥0∞) ^ 2 * (clampMesh P H b T j + clampMesh P H b T j') := by sorry
