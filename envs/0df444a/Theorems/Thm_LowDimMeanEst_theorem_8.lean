-- Prove2me | Theorems.Thm_LowDimMeanEst_theorem_8
-- name    : LowDimMeanEst.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:01:54.945041+00:00
-- url     : https://prove2.me/theorems/fc8a29db-e2de-440d-8096-580960e092ea
-- title:
--   Theorem 8 — large-trace case: $P[\|{-\mu}+\frac1n\sum(1-w_i)x_i\|\ge(1+\|\mu\|)\sqrt{2\log(1/\delta)/n},\ \mathrm{Tr}(A)\ge R]\le\delta/100$
-- statement:
--   **Theorem 8.** There is a universal $\delta_0\in(0,1)$ such that the following holds for all $d,n\ge1$ and $\delta\in(0,\delta_0)$. Let $D$ be a distribution on $\mathbb R^d$ with mean $\mu$ and covariance $\Sigma\preceq I$ (no bound on $\|\mu\|$), and $x_1,\dots,x_n$ i.i.d. from $D$. With $L=\log\frac1\delta$ and $R=25000000\,dL/n$, the probability that some trimming matrix $A$ of the samples has $\mathrm{Tr}(A)\ge R$ and
--
--   $$\Big\|-\mu+\frac1n\sum_i\big(1-\min(1,x_i^\top Ax_i)\big)x_i\Big\|\ \ge\ (1+\|\mu\|)\sqrt{\frac{2L}n} \tag{8}$$
--
--   is at most $\delta/100$.
--
--   This is the large-trace half of the case split in the proof of Theorem 6.
--
--   Differences from the source:
--   - generalization: the trimming matrix A computed by Algorithm 2 (Lemma 3) → every A with IsTrimmingMatrix: A ⪰ 0, Σ min(1, x_i^⊤Ax_i) = (1/3)log(1/δ), Lemma 3's maximality; reason: the computed matrix has these properties (Lemma 3 and the weight sum of Algorithm 2), so the statement specializes to it; A is not unique (p.9)
--   - encoding: δ upper bounded by a small universal constant → ∃ δ0 ∈ (0, 1) chosen before d, n, D, and δ ∈ (0, δ0); reason: a universal constant
--   - encoding: the probability of an event about "the" A → outer measure of the event "some trimming matrix A satisfies …"; reason: the event need not be measurable; covers every selection of A
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Theorem 8, p.13 (restated p.44; proof pp.44–47)

import Mathlib
import Definitions.Def_LowDimMeanEst_TrimmingMatrix
import Definitions.Def_LowDimMeanEst_Parameters

open MeasureTheory

namespace LowDimMeanEst

/-- **Theorem 8**, p.13 (restated p.44; proof pp.44–47).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose the probability parameter δ is upper bounded by some small universal constant. Now consider
a distribution D on ℝᵈ with mean µ and covariance matrix Σ ⪯ I. Let x₁, …, xₙ denote n i.i.d.
samples drawn from D. Let R = 25000000d log(1/δ)/n. Consider the trimming matrix A implicitly
computed by Algorithm 2 (Lemma 3) with input {xᵢ} and parameter δ. It follows that
P[ ∥−µ + (1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ)) xᵢ∥ ≥ (1 + ∥µ∥)√(2 log(1/δ)/n) and Tr(A) ≥ R ] ≤ δ/100 (8)"

**Formalization Note.** `∃ δ0` before everything. No bound on `‖µ‖` is assumed, as printed. The bad
event ranges over every trimming matrix (`IsTrimmingMatrix`), as an outer measure. `d ≥ 1`,
`n ≥ 1` standing.
-/
theorem theorem_8 :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1 ∧
      ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < δ0 →
        ∀ (D : Measure (E d)) [IsProbabilityMeasure D], CovLe D 1 →
          (Measure.pi fun _ : Fin n => D)
              {x | ∃ A : E d →L[ℝ] E d, IsTrimmingMatrix x δ A ∧
                (1 + ‖popMean D‖) * Real.sqrt (2 * logInv δ / n) ≤
                  ‖-popMean D + trimmedMean x A‖ ∧
                paramR d n δ ≤ tr A} ≤
            ENNReal.ofReal (δ / 100) := by sorry

end LowDimMeanEst
