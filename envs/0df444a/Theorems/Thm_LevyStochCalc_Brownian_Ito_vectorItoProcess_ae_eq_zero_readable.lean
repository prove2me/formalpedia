-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_vectorItoProcess_ae_eq_zero_readable
-- name    : LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:08.803457+00:00
-- url     : https://prove2.me/theorems/2c299ed7-02cc-4215-b871-f99239baed20
-- title:
--   Vector Itô Process at Initial Time
-- statement:
--   This states that a vector Itô process equals its initial value almost everywhere at time zero.
--
--   Let $P$ be a probability measure, let $W$ be a multidimensional Brownian motion, and let $\mathcal F$ be a filtration with the required Brownian-coordinate properties. Let $H$ and $b$ be measurable and progressively measurable coefficient and drift families, and assume that each coefficient has finite squared energy on every interval $[0,T]$ with $T>0$. For an initial state $X_0:\Omega\to\mathbb R^n$,
--
--   $$\operatorname{vectorItoProcess}(0)=X_0\quad\text{a.e. }[P].$$
--
--   The equality is an almost-everywhere equality of functions $\Omega\to(\mathbb R^n)$, with coordinates indexed by `Fin n`. This provides the initial-time property used by vector Itô version constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem vectorItoProcess_ae_eq_zero (W : Multidim.MultidimBrownianMotion P d)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
--       {H : Fin n → Fin d → Ω → ℝ → ℝ}
--       (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
--       (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
--       (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (X₀ : Ω → Fin n → ℝ) (b : Fin n → Ω → ℝ → ℝ) :
--       vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ b 0 =ᵐ[P] X₀
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionLimit`](https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Previous: [`exists_seq_clampMesh_window_lt`](https://prove2.me/theorems/b2eb4ef5-6631-48e3-9006-913e761e4fc6) · Next: [`exists_isVectorItoVersion_of_unbounded`](https://prove2.me/theorems/31d4b1e5-43c0-487e-8cd2-7922775543cc).
--
--   [Source excerpt, lines 157–166](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L157-L166) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L156-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionLimit`, declaration `LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_readable (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin n → ℝ) (b : Fin n → Ω → ℝ → ℝ) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ b 0 =ᵐ[P] X₀ := by sorry
