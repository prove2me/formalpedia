-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_weighted_polarQuadVarSum_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_weighted_polarQuadVarSum_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:37.141003+00:00
-- url     : https://prove2.me/theorems/194ed6f8-bb43-4c00-b88b-c7080958b1e9
-- title:
--   Weighted Polarized Increment Sum Bound
-- statement:
--   Let $t:\mathbb N\to\mathbb R$ satisfy $0\le t_0$ and $t_k<t_{k+1}$. Let $g_k:\Omega\to\mathbb R$ be strongly $\mathcal F.\mathrm{rightCont}_{t_k}$-measurable, with $D\ge0$ and $|g_k|\le D$. Under the stated hypotheses on $H_1,H_2$ and $C\ge0$, for every $N\in\mathbb N$,
--
--   $$\int\left(\sum_{i<N}g_i\,\mathrm{polarQuadVarIncrement}_{t_i,t_{i+1}}(H_1,H_2)\right)^2dP
--   \le D^2\,3\bigl(2(6+\gamma_4)+2\bigr)(2C)^4
--   \sum_{i<N}(t_{i+1}-t_i)^2.$$
--
--   This is the finite-grid second-moment estimate for conditionally centered polarized increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_weighted_polarQuadVarSum_le
--       (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
--       (g : ℕ → Ω → ℝ)
--       (hg : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (t k)) (g k))
--       {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (N : ℕ) :
--       ∫ ω, (∑ i ∈ Finset.range N, g i ω
--           * polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2 ∂P
--         ≤ D ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
--           * ∑ i ∈ Finset.range N, (t (i + 1) - t i) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`condExp_polarQuadVarIncrement`](https://prove2.me/theorems/90ba8838-f516-4c4a-a54e-03f7270ecbb4), [`integral_sq_polarQuadVarIncrement_le`](https://prove2.me/theorems/3e500a78-fa1d-4509-8fce-e931788339ed), [`memLp_two_polarQuadVarIncrement`](https://prove2.me/theorems/e1f3d644-9e95-4545-bc1a-84c062eb6f44), [`stronglyMeasurable_polarQuadVarIncrement`](https://prove2.me/theorems/257fc5bd-0d48-42b0-a71b-4fcd26b462bd), [`integral_sq_sum_of_condExp_eq_zero`](https://prove2.me/theorems/fbb3abb4-5edb-4d91-878c-9d2326ca20d8).
--
--   Previous: [`integral_sq_polarQuadVarIncrement_le`](https://prove2.me/theorems/3e500a78-fa1d-4509-8fce-e931788339ed).
--
--   [Source excerpt, lines 317–325](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L317-L325) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L313-L404 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.PolarisedQuadVar`, declaration `LevyStochCalc.Brownian.Ito.integral_sq_weighted_polarQuadVarSum_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)
include hℱ hma hpa hqa hC0 hCH₁ hCH₂

theorem LevyStochCalc.Brownian.Ito.integral_sq_weighted_polarQuadVarSum_le_readable
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ)
    (hg : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (t k)) (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (N : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range N, g i ω
        * polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
        * ∑ i ∈ Finset.range N, (t (i + 1) - t i) ^ 2 := by sorry
