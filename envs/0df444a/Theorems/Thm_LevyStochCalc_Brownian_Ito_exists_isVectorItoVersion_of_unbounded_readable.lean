-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion_of_unbounded_readable
-- name    : LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:07.327026+00:00
-- url     : https://prove2.me/theorems/31d4b1e5-43c0-487e-8cd2-7922775543cc
-- title:
--   Existence of a Continuous Adapted Vector Itô Version
-- statement:
--   This asserts existence of a continuous adapted version of a vector Itô process with unbounded coefficients.
--
--   Let $P$ be a probability measure, $W$ a $d$-dimensional Brownian motion, and $\mathcal F$ a filtration such that: (1) every Brownian coordinate has the required Brownian filtration; (2) $\mathcal F_0\le\mathcal F_t$ whenever $t\le0$; and (3) every measurable $P$-null set is measurable in $\mathcal F_0$. Let $H$ be measurable and progressively measurable, with squared coefficient energy strictly below $\top$ on every positive window. Let $X_0:\Omega\to\mathbb R^n$ be $\mathcal F_0$-measurable, and let the drift $b$ be measurable and progressively measurable with finite squared energy on every positive window.
--
--   Then there exists $X:\mathbb R\to\Omega\to\mathbb R^n$ such that
--
--   $$X\text{ is a continuous adapted version of the vector Itô process driven by }(H,b),$$
--
--   in the precise sense of `IsVectorItoVersion`. The theorem is an existence result for finite-dimensional vector processes; it does not assert uniqueness.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_isVectorItoVersion_of_unbounded
--       (W : Multidim.MultidimBrownianMotion P d)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
--       (H : Fin n → Fin d → Ω → ℝ → ℝ)
--       (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
--       (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
--       (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
--       (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
--       (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
--       (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
--       ∃ X : ℝ → Ω → Fin n → ℝ,
--         IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionLimit`](https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Selected supporting theorems: [`clampMesh_mono_window`](https://prove2.me/theorems/17031eaf-0282-46a9-a32a-db61ccb38eec), [`exists_isVectorItoVersion`](https://prove2.me/theorems/4eca63c9-5730-45f7-b754-fdcf7d1ac296), [`exists_seq_clampMesh_window_lt`](https://prove2.me/theorems/b2eb4ef5-6631-48e3-9006-913e761e4fc6), [`le_add_inv_mul_sq`](https://prove2.me/theorems/55fc83fc-8bfe-43c9-9ba2-4e5fb4a6199b), [`lintegral_iSup_sq_norm_clamp_version_sub_le`](https://prove2.me/theorems/504b07f4-fd56-41ea-9704-d91515922d85).
--
--   Previous: [`vectorItoProcess_ae_eq_zero`](https://prove2.me/theorems/2c299ed7-02cc-4215-b871-f99239baed20).
--
--   [Source excerpt, lines 190–207](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L190-L207) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L187-L516 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionLimit`, declaration `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}

theorem LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded_readable
    (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by sorry
