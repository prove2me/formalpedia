-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_weighted_crossSum_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:11.045999+00:00
-- url     : https://prove2.me/theorems/5d328781-1a8c-43bf-be55-0a5141e07939
-- title:
--   Second-Moment Bound for Weighted Cross-Increment Sums
-- statement:
--   This theorem bounds the second moment of a weighted sum of cross increments from two distinct Brownian coordinates.
--
--   Let $W$ be a multidimensional Brownian motion whose coordinates are Brownian relative to a filtration $\mathcal F$. Let $H,K$ be jointly measurable, progressively measurable integrands with finite squared-norm integrals on every positive finite time interval. Assume $C_H,C_K,D\ge0$, $|H(\omega,s)|\le C_H$, $|K(\omega,s)|\le C_K$, and let $i\ne j$ be coordinate indices. Let $t:\mathbb N\to\mathbb R$ satisfy $0\le t_0$ and $t_k<t_{k+1}$, and let $g_k$ be strongly measurable and bounded by $D$.
--
--   Then, for every $n$,
--
--   $$
--   \int\left(\sum_{k<n}g_k\,\Delta_k^{i,j}\right)^2dP
--   \le D^2\frac{(6+\mathsf g_4)(C_H^4+C_K^4)}{2}
--   \sum_{k<n}(t_{k+1}-t_k)^2,
--   $$
--
--   where $\Delta_k^{i,j}$ is the product of the two Itô-integral increments over $[t_k,t_{k+1}]$. This is a reusable martingale-difference estimate for cross-variation sums.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_weighted_crossSum_le {i j : Fin d} (hij : i ≠ j)
--       (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
--       (g : ℕ → Ω → ℝ) (hg : ∀ k, StronglyMeasurable[ℱ (t k)] (g k))
--       {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
--       ∫ ω, (∑ k ∈ Finset.range n, g k ω *
--           crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P
--         ≤ D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
--           * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossVariationSum`](https://prove2.me/theorems/a1ff2b05-5818-415f-a2f2-029a029a1d6c).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`condExp_mul_cross_increment_eq_zero`](https://prove2.me/theorems/99d0dc79-016a-4aa6-9626-db8a484a0275), [`integrable_sq_mul_and_le`](https://prove2.me/theorems/9194c79a-683c-4a17-8bf7-6d933792ea69), [`integral_sub_pow_four_le`](https://prove2.me/theorems/12ff2533-d8a3-4978-a4f3-a45469d7fa7c), [`integral_sq_sum_of_condExp_eq_zero`](https://prove2.me/theorems/fbb3abb4-5edb-4d91-878c-9d2326ca20d8).
--
--   Previous: [`integrable_sq_mul_and_le`](https://prove2.me/theorems/9194c79a-683c-4a17-8bf7-6d933792ea69).
--
--   [Source excerpt, lines 141–148](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossVariationSum.lean#L141-L148) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossVariationSum.lean#L137-L223 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossVariationSum`, declaration `LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariationSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariationSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
variable {d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)
include hCH0 hCH hCK0 hCK

theorem LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le_readable {i j : Fin d} (hij : i ≠ j)
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ) (hg : ∀ k, StronglyMeasurable[ℱ (t k)] (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, g k ω *
        crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
        * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by sorry
