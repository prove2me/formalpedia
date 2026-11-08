-- Prove2me | Theorems.Thm_LowDimMeanEst_corollary_7
-- name    : LowDimMeanEst.corollary_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:54.143202+00:00
-- url     : https://prove2.me/theorems/1cbed5e6-626a-4aac-99a4-f5e163d49a09
-- title:
--   Corollary 7 — small-trace case: $P[\mathrm{Tr}(A)\le R,\ \|{-\mu}+\frac1n\sum(1-w_i)x_i\|\ge\frac{1+\eta}{1-1/\log\log(1/\delta)}\sqrt{2\log(1/\delta)/n}]\le\delta/25$
-- statement:
--   **Corollary 7.** There are universal constants $\delta_0\in(0,1)$ and $C>0$ such that the following holds for all $d,n\ge1$ and $\delta\in(0,\delta_0)$. Let $D$ be a distribution on $\mathbb R^d$ with mean $\mu$, $\|\mu\|\le1$ and covariance $\Sigma\preceq I$, and $x_1,\dots,x_n$ i.i.d. from $D$. With $L=\log\frac1\delta$, $LL=\log\log\frac1\delta$, $R=25000000\,dL/n$ and
--
--   $$\eta=C\Big(\sqrt{\|\mu\|^2+\tfrac dL}+\tfrac1{LL}+\tfrac{d^2(\log d+LL)}{L}\sqrt{1+\tfrac dL}\Big),$$
--
--   the probability that some trimming matrix $A$ of the samples has $\mathrm{Tr}(A)\le R$ and
--
--   $$\Big\|-\mu+\frac1n\sum_i\big(1-\min(1,x_i^\top Ax_i)\big)x_i\Big\|\ \ge\ \frac{1+\eta}{1-1/LL}\sqrt{\frac{2L}n} \tag{7}$$
--
--   is at most $\delta/25$.
--
--   This is the small-trace half of the case split in the proof of Theorem 6.
--
--   Differences from the source:
--   - generalization: the trimming matrix A computed by Algorithm 2 (Lemma 3) → every A with IsTrimmingMatrix: A ⪰ 0, Σ min(1, x_i^⊤Ax_i) = (1/3)log(1/δ), Lemma 3's maximality; reason: the computed matrix has these properties (Lemma 3 and the weight sum of Algorithm 2), so the statement specializes to it; A is not unique (p.9)
--   - encoding: δ small universal constant; η = O(·) → ∃ δ0 ∈ (0, 1), C > 0 before d, n, D; reason: universal constants
--   - encoding: the probability of an event about "the" A → outer measure of the event "some trimming matrix A satisfies …"; reason: the event need not be measurable; covers every selection of A
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Corollary 7, p.13 (restated pp.23, 39; proof pp.39–41)

import Mathlib
import Definitions.Def_LowDimMeanEst_TrimmingMatrix
import Definitions.Def_LowDimMeanEst_Parameters

open MeasureTheory

namespace LowDimMeanEst

/-- **Corollary 7**, p.13 (restated pp.23, 39; proof pp.39–41).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose the probability parameter δ is upper bounded by some small universal constant. Now consider
a distribution D in ℝᵈ with mean µ satisfying ∥µ∥ ≤ 1 and covariance matrix Σ ⪯ I. Let x₁, …, xₙ
denote n i.i.d. samples drawn from D. Consider the trimming matrix A implicitly computed by
Algorithm 2 (Lemma 3) with input {xᵢ} and parameter δ. Let R = 25000000d log(1/δ)/n and
η = O(√(∥µ∥² + d/log(1/δ)) + 1/log log(1/δ) + (d²(log d + log log(1/δ))/log(1/δ)) √(1 + d/log(1/δ))).
It follows that P[ Tr(A) ≤ R and ∥−µ + (1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ)) · xᵢ∥ ≥
((1 + η)/(1 − 1/log log(1/δ))) √(2 log(1/δ)/n) ] ≤ δ/25 (7)"

**Formalization Note.** `∃ δ0, C` before everything; `η = etaCor C d ‖µ‖² δ`. The bad event ranges
over every trimming matrix (`IsTrimmingMatrix`), as an outer measure. `d ≥ 1`, `n ≥ 1` standing.
-/
theorem corollary_7 :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ δ0 < 1 ∧ 0 < C ∧
      ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < δ0 →
        ∀ (D : Measure (E d)) [IsProbabilityMeasure D], CovLe D 1 → ‖popMean D‖ ≤ 1 →
          (Measure.pi fun _ : Fin n => D)
              {x | ∃ A : E d →L[ℝ] E d, IsTrimmingMatrix x δ A ∧ tr A ≤ paramR d n δ ∧
                (1 + etaCor C d (‖popMean D‖ ^ 2) δ) / (1 - 1 / loglogInv δ) *
                    Real.sqrt (2 * logInv δ / n) ≤
                  ‖-popMean D + trimmedMean x A‖} ≤
            ENNReal.ofReal (δ / 25) := by sorry

end LowDimMeanEst
