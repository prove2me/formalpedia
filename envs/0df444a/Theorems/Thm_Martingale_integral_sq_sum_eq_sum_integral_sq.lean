-- Prove2me | Theorems.Thm_Martingale_integral_sq_sum_eq_sum_integral_sq
-- name    : Martingale.integral_sq_sum_eq_sum_integral_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T00:04:47.232353+00:00
-- url     : https://prove2.me/theorems/b94fec3c-f286-4a10-922c-e4c3238438e0
-- title:
--   Pythagoras for martingale differences: $\mathbb{E}[(\sum V_j)^2] = \sum \mathbb{E}[V_j^2]$
-- statement:
--   **Pythagoras' theorem for martingale differences.** Let $(\mathcal{F}_j)_{j\ge0}$ be a filtration on a finite measure space and let $(V_j)_{j\ge0}$ be a square-integrable martingale difference sequence: each $V_j$ is $\mathcal{F}_{j+1}$-measurable with $\mathbb{E}[V_j \mid \mathcal{F}_j] = 0$ almost everywhere. Then for every $n$ the second moment of the partial sum is the sum of the second moments:
--   $$\mathbb{E}\Bigl[\Bigl(\sum_{j<n} V_j\Bigr)^{2}\Bigr] = \sum_{j<n} \mathbb{E}\bigl[V_j^{2}\bigr].$$
--   Expanding the square produces $n^2$ terms, and all the off-diagonal ones vanish because distinct martingale increments are orthogonal in $L^2$. The identity is the exact analogue of the additivity of variance for independent summands, but requires no independence at all: it is the reason that the Fisher information of a sequentially observed model is the sum of the per-observation informations, and the reason that the quadratic variation, rather than any independence structure, is the right normalisation in the martingale central limit theorem.
-- source:
--   D. Williams, Probability with Martingales, Cambridge University Press, 1991, Theorem 12.1 (the sum of squares / orthogonality of increments); P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press, 1980, Section 2.1.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal NNReal

theorem Martingale.integral_sq_sum_eq_sum_integral_sq {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j, MemLp (V j) 2 μ)
    (hadapt : ∀ j, StronglyMeasurable[ℱ (j + 1)] (V j))
    (hmds : ∀ j, μ[V j | ℱ j] =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range n, V j ω) ^ 2 ∂μ
      = ∑ j ∈ Finset.range n, ∫ ω, (V j ω) ^ 2 ∂μ := by sorry
