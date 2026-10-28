-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion_readable
-- name    : LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:32.49647+00:00
-- url     : https://prove2.me/theorems/4eca63c9-5730-45f7-b754-fdcf7d1ac296
-- title:
--   Continuous Adapted Vector Itô Version
-- statement:
--   Let $W$ be a $d$-dimensional Brownian motion, let $\mathcal F$ satisfy the Brownian-filtration hypotheses, and let $H_{pk}$ be measurable, progressively measurable, square-integrable coefficients with a uniform bound $C$. Let $X_0:\Omega\to\mathbb R^n$ have measurable coordinates, and let $b_p$ be measurable and progressively measurable with $|b_p(\omega,s)|\le B$ for some $B\ge0$. Assume the filtration is constant before time $0$ in the stated sense and contains measurable null sets. Then there exists
--
--   $$
--   X:\mathbb R\times\Omega\to(\mathrm{Fin}\,n\to\mathbb R)
--   $$
--
--   which is a continuous adapted version of the vector Itô process `IsVectorItoVersion W ℱ hcoord H ... X₀ bdrift X`. The theorem asserts existence of the version and does not specify a uniqueness statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_isVectorItoVersion
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
--       (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
--       (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
--       {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
--       ∃ X : ℝ → Ω → Fin n → ℝ,
--         IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoVersionExists`](https://prove2.me/theorems/efbe558e-34b1-48bc-972e-346434525ee9).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`exists_continuousAdapted_modification`](https://prove2.me/theorems/f0d85cba-26cf-42ee-a24a-f69b68bf4f0b), [`abs_setIntegral_Icc_sub_le`](https://prove2.me/theorems/a024dc62-1949-4b29-9d3e-69c1cee958e2).
--
--   [Source excerpt, lines 50–58](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoVersionExists.lean#L50-L58) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoVersionExists.lean#L47-L94 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoVersionExists`, declaration `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoVersionExists.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
  (hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k))
  (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_readable
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by sorry
