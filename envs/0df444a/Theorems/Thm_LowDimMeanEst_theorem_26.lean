-- Prove2me | Theorems.Thm_LowDimMeanEst_theorem_26
-- name    : LowDimMeanEst.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:00:00.461714+00:00
-- url     : https://prove2.me/theorems/e375473d-5d1c-40e4-8342-1b3374bc9a32
-- title:
--   Theorem 26 — for every small-trace trimming matrix and fixed unit $z$: events F, T, B and $F(x,A,z,a^{(A)},b^{(A)},t^{(A)})\ge0$ have probability $\le\delta/(100d\log\frac1\delta)^{d^2}$
-- statement:
--   **Theorem 26.** There are universal constants $\delta_0\in(0,1)$ and $C>0$ such that the following holds for all $d,n\ge1$ and $\delta\in(0,\delta_0)$. Let $D$ be a distribution on $\mathbb R^d$ with mean $\mu$, $\|\mu\|\le1$ and covariance $\Sigma\preceq I$, and $x_1,\dots,x_n$ i.i.d. from $D$. Let $L=\log\frac1\delta$, $R=25000000\,dL/n$ and
--
--   $$\eta=C\Big(\sqrt{\|\mu\|^2+\tfrac dL}+\tfrac1{LL}+\tfrac{d^2(\log d+LL)}{L}\sqrt{1+\tfrac dL}\Big).$$
--
--   There are functions $a^{(A)}\in\mathbb R$, $b^{(A)}\ge0$, $t^{(A)}>0$ of the matrix $A$ such that for every fixed unit vector $z$, the probability that some trimming matrix $A$ of the samples satisfies events F, T, B, $\mathrm{Tr}(A)\le R$ and
--
--   $$a^{(A)}\Big(\sum_i m_i-\tfrac L3\Big)+b^{(A)}\sum_i(1-m_i)x_i^\top Ax_i-b^{(A)}\mathrm{Tr}(A)\sum_i(1-m_i)(x_i\cdot z)^2+t^{(A)}\Big(\frac1n\sum_i(1-m_i)(x_i\cdot z)-\mu\cdot z-(1+\eta)\sqrt{\tfrac{2L}n}\Big)\ \ge0, \tag{28}$$
--
--   with $m_i=\min(1,x_i^\top Ax_i)$, is at most $\delta/(100\,d\,L)^{d^2}$.
--
--   This is Lemma 9 made simultaneous over all small-trace matrices, for a fixed direction; a second net over directions gives Corollary 7.
--
--   **Formalization Note** The left-hand side of (28) is $F(x,A,z,a,b,t)$ of Definition 10. Events F, T, B are Definitions 15, 21, 22.
--
--   Differences from the source:
--   - generalization: the trimming matrix A computed by Algorithm 2 (Lemma 3) → every A with IsTrimmingMatrix: A ⪰ 0, Σ min(1, x_i^⊤Ax_i) = (1/3)log(1/δ), Lemma 3's maximality; reason: the computed matrix has these properties (Lemma 3 and the weight sum of Algorithm 2), so the statement specializes to it; A is not unique (p.9)
--   - reading: event B: α ≤ O(1 + d/log(1/δ)) (Definition 22) → α ≤ (10¹⁰/3)(1 + d/log(1/δ)), α the largest trimmed empirical variance (1/n)Σ(1 − min(1, x_i^⊤Ax_i))⟨x_i, v⟩²; reason: Definition 22 refers to the bound established in Lemma 44, which is Lemma 43 applied with Tr(A) ≥ 10⁻¹⁰ log(1/δ)/(n(1 + d/log(1/δ))) (p.84); α read as in Lemma 43's proof
--   - encoding: δ small universal constant; η = O(·) → ∃ δ0 ∈ (0, 1), C > 0 before d, n, D; reason: universal constants
--   - encoding: parameters a^(A), b^(A) ≥ 0, t^(A) > 0 → functions of the matrix, chosen after d, n, δ, D and before z, with b ≥ 0, t > 0 on every matrix; reason: the superscript (A) marks dependence on A only
--   - encoding: the probability of an event about "the" A → outer measure of the event "some trimming matrix A satisfies …"; reason: the event need not be measurable; covers every selection of A
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Theorem 26, pp.31–32 (proof pp.32–39)

import Mathlib
import Definitions.Def_LowDimMeanEst_Events
import Definitions.Def_LowDimMeanEst_ChernoffF

open MeasureTheory

namespace LowDimMeanEst

/-- **Theorem 26**, pp.31–32 (proof pp.32–39).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose the probability parameter δ is upper bounded by some small universal constant. Now consider
a distribution D in ℝᵈ with mean µ satisfying ∥µ∥ ≤ 1 and covariance matrix Σ ⪯ I. Let x₁, …, xₙ
denote n i.i.d. samples drawn from D. Consider the trimming matrix A implicitly computed by
Algorithm 2 (Lemma 3) with input {xᵢ} and parameter δ. Let R = 25000000d log(1/δ)/n and
η = O(√(∥µ∥² + d/log(1/δ)) + 1/log log(1/δ) + (d²(log d + log log(1/δ))/log(1/δ)) √(1 + d/log(1/δ))).
There exist parameters a^(A) ∈ ℝ, b^(A) ≥ 0, and t^(A) > 0 such that for any fixed unit vector z,
P[ Events F, T, B hold and Tr(A) ≤ R and a^(A)(Σᵢ min(1, xᵢ⊤Axᵢ) − (1/3) log(1/δ))
+ b^(A)(Σᵢ (1 − min(1, xᵢ⊤Axᵢ)) xᵢ⊤Axᵢ) − b^(A) Tr(A)(Σᵢ (1 − min(1, xᵢ⊤Axᵢ))(xᵢ · z)²)
+ t^(A)((1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ))(xᵢ · z) − µ · z − (1 + η)√(2 log(1/δ)/n)) ≥ 0 ]
≤ δ/(100d log(1/δ))^{d²}. (28)"

**Formalization Note.**
* "Some small universal constant" and the `O(·)` of `η` are `∃ δ0, C` before everything;
  `η = etaCor C d ‖µ‖² δ`.
* `a^(A), b^(A), t^(A)` are functions of the matrix `A`, chosen after `d, n, δ, D` and before `z`,
  with `b ≥ 0` and `t > 0` on every matrix.
* The expression in (28) is `chernoffF` (Definition 10) with this `η` and `µ`; the bad event is
  "some trimming matrix `A` satisfies all the conditions", over every `A` with `IsTrimmingMatrix`
  (outer measure). Events F, T, B are Definitions 15, 21, 22; `R` is `paramR` (Table 1).
* `d ≥ 1`, `n ≥ 1` are standing assumptions.
-/
theorem theorem_26 :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ δ0 < 1 ∧ 0 < C ∧
      ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < δ0 →
        ∀ (D : Measure (E d)) [IsProbabilityMeasure D], CovLe D 1 → ‖popMean D‖ ≤ 1 →
          ∃ a b t : (E d →L[ℝ] E d) → ℝ, (∀ A, 0 ≤ b A) ∧ (∀ A, 0 < t A) ∧
            ∀ z : E d, ‖z‖ = 1 →
              (Measure.pi fun _ : Fin n => D)
                  {x | ∃ A : E d →L[ℝ] E d, IsTrimmingMatrix x δ A ∧ EventF x δ ∧ EventT x δ ∧
                    EventB x δ A ∧ tr A ≤ paramR d n δ ∧
                    0 ≤ chernoffF δ (etaCor C d (‖popMean D‖ ^ 2) δ) (popMean D) x A z
                      (a A) (b A) (t A)} ≤
                ENNReal.ofReal (δ / (100 * d * logInv δ) ^ (d ^ 2)) := by sorry

end LowDimMeanEst
