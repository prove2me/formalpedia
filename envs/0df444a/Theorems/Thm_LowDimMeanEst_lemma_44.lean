-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_44
-- name    : LowDimMeanEst.lemma_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:05.99188+00:00
-- url     : https://prove2.me/theorems/fd84e016-146e-4e01-b35f-4eefda208462
-- title:
--   Lemma 44 — w.p. $\ge1-\delta/100$, $\mathrm{Tr}(A)\ge10^{-10}\log(1/\delta)/(n(1+d/\log(1/\delta)))$, and then $\alpha\le\frac{10^{10}}3(1+d/\log(1/\delta))$
-- statement:
--   **Lemma 44.** There is a universal $\delta_0\in(0,1)$ such that the following holds for all $d,n\ge1$ and $\delta\in(0,\delta_0)$. Let $D$ be a distribution on $\mathbb R^d$ with mean $\mu$, $\|\mu\|\le1$ and covariance $\Sigma\preceq I$, and let $x_1,\dots,x_n$ be i.i.d. from $D$. Write $L=\log\frac1\delta$.
--
--   1. With probability at least $1-\delta/100$, every trimming matrix $A$ of the samples satisfies
--   $$\mathrm{Tr}(A)\ \ge\ \frac{10^{-10}L}{n(1+d/L)} .$$
--   2. If a trimming matrix satisfies this bound, then the trimmed empirical variance satisfies, for every unit $v$,
--   $$\alpha_v=\frac1n\sum_i\big(1-\min(1,x_i^\top Ax_i)\big)(x_i\cdot v)^2\ \le\ \frac{10^{10}}3\Big(1+\frac dL\Big).$$
--
--   The trace bound is what allows Lemma 9 to be applied to the trimming matrix, and the variance bound is half of event B.
--
--   **Formalization Note** The paper's "$\alpha\le O(1+d/\log(1/\delta))$" is stated with the constant its proof gives (Lemma 43 with this trace bound, p.84). The failure event ranges over every trimming matrix and is measured by outer measure.
--
--   Differences from the source:
--   - generalization: the trimming matrix A computed by Algorithm 2 (Lemma 3) → every A with IsTrimmingMatrix: A ⪰ 0, Σ min(1, x_i^⊤Ax_i) = (1/3)log(1/δ), Lemma 3's maximality; reason: the computed matrix has these properties (Lemma 3 and the weight sum of Algorithm 2), so the statement specializes to it; A is not unique (p.9)
--   - generalization: α ≤ O(1 + d/log(1/δ)) with high probability → α ≤ (10¹⁰/3)(1 + d/log(1/δ)) deterministically whenever the trace bound holds; reason: the explicit constant is the one the proof derives from Lemma 43, and the trace bound holds w.p. 1 − δ/100, so this implies the source's claim
--   - encoding: δ upper bounded by a small universal constant → ∃ δ0 ∈ (0, 1) chosen before d, n, D, and δ ∈ (0, δ0); reason: a universal constant
--   - encoding: the probability of an event about "the" A → outer measure of the event "some trimming matrix A satisfies …"; reason: the event need not be measurable; covers every selection of A
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 44, p.83 (proof p.84)

import Mathlib
import Definitions.Def_LowDimMeanEst_TrimmingMatrix

open MeasureTheory

namespace LowDimMeanEst

/-- **Lemma 44**, p.83 (proof p.84).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose the failure probability δ is bounded above by a sufficiently small universal constant. Now
consider a distribution D on ℝᵈ with mean µ satisfying ∥µ∥ ≤ 1 and covariance matrix Σ ⪯ I. Let
x₁, …, xₙ denote n i.i.d. samples drawn from D. Consider the trimming matrix A implicitly computed by
Algorithm 2 (Lemma 3) with input {xᵢ} and parameter δ. With probability at least 1 − δ/100,
Tr(A) ≥ 10⁻¹⁰ log(1/δ)/(n(1 + d/log(1/δ))). Moreover, if this occurs, the trimmed empirical variance
α (defined in Algorithm 2) is O_d(1). In particular, α ≤ O(1 + d/log(1/δ)) with high probability."

**Formalization Note.**
* "Sufficiently small universal constant": `∃ δ0 ∈ (0, 1)` before `d, n, D`.
* The failure event is "some trimming matrix `A` (`IsTrimmingMatrix`) has `Tr(A)` below the bound".
  It need not be measurable; the measure of a set is its outer measure.
* "Moreover … In particular": the deterministic implication, with the `O(·)` read as the constant
  `10¹⁰/3` that Lemma 43 gives from the trace bound (p.84), and `α` the largest trimmed empirical
  variance `max_{‖v‖=1} (1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ))⟨xᵢ, v⟩²`.
-/
theorem lemma_44 :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1 ∧
      ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < δ0 →
        ∀ (D : Measure (E d)) [IsProbabilityMeasure D], CovLe D 1 → ‖popMean D‖ ≤ 1 →
          (Measure.pi fun _ : Fin n => D)
              {x | ∃ A : E d →L[ℝ] E d, IsTrimmingMatrix x δ A ∧
                tr A < (10 : ℝ) ^ (-10 : ℤ) * logInv δ / (n * (1 + d / logInv δ))} ≤
            ENNReal.ofReal (δ / 100) ∧
          ∀ (x : Fin n → E d) (A : E d →L[ℝ] E d), IsTrimmingMatrix x δ A →
            (10 : ℝ) ^ (-10 : ℤ) * logInv δ / (n * (1 + d / logInv δ)) ≤ tr A →
            ∀ v : E d, ‖v‖ = 1 →
              (1 / (n : ℝ)) * trimmedQuad x A v ≤ ((10 : ℝ) ^ 10 / 3) * (1 + d / logInv δ) := by sorry

end LowDimMeanEst
