-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_12
-- name    : LowDimMeanEst.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:54:52.781207+00:00
-- url     : https://prove2.me/theorems/f216e06d-9cc9-4dd2-9dbe-49db0b006516
-- title:
--   Lemma 12 — $\mathbb E[e^{F(x,A,z,a,b,t)}]\le e^{r\log(1/\delta)}$ for every feasible $(q_1,q_2)$ of program (15), $c=n\mathrm{Tr}(A)/\log(1/\delta)$
-- statement:
--   **Lemma 12.** Let $\delta\in(0,1)$, $\eta>0$, $\gamma\ge0$, and let $D$ be a distribution on $\mathbb R^d$ with mean $\mu$ and second moment $\mathbb E[XX^\top]\preceq(1+\gamma)I$. Let $x_1,\dots,x_n$ be i.i.d. samples from $D$, $z$ a unit vector, $A\succeq0$ a nonzero matrix, $a,b,t\in\mathbb R$, and put $L=\log\frac1\delta$, $c=n\,\mathrm{Tr}(A)/L$, $s=t/\sqrt{nL}$. If $q_1,q_2\ge0$ satisfy
--
--   $$1+s\,x_2+\frac{q_1}{c}x_1+q_2x_2^2\ \ge\ e^{\,a+\left(-a+\left(bx_1-bcx_2^2+s\,x_2\right)\right)(1-\min(1,x_1))}\qquad\forall x_1\ge0,\ x_2\in\mathbb R, \tag{15}$$
--
--   then, with $F$ as in Definition 10 (with this $\eta$ and $\mu$),
--
--   $$\mathbb E_{x_1,\dots,x_n\sim D}\big[e^{F(x,A,z,a,b,t)}\big]\ \le\ e^{rL},\qquad r=(1+\gamma)(q_1+q_2)-\frac a3-(1+\eta)\,s\sqrt2 .$$
--
--   Since this holds for every feasible $(q_1,q_2)$, it bounds the moment generating function by $e^{rL}$ with $r$ the optimal value of the program, as stated in the paper. It converts the Chernoff bound of Lemma 11 into the two-dimensional program solved by Lemma 13.
--
--   **Formalization Note** The expectation is the Lebesgue integral of the nonnegative function $e^F$, so integrability is not an issue. The hypothesis is on the uncentred second moment.
--
--   Differences from the source:
--   - encoding: r the objective value (minimum) of program (15) → the bound holds for every feasible (q₁, q₂) with r its objective; reason: equivalent to the bound by the infimum, without assuming it is attained
--   - encoding: E[e^F] → lower Lebesgue integral of e^F against the product measure; reason: same value for a nonnegative integrand
--   - encoding: n samples → 1 ≤ n; reason: n is a number of samples; excludes only n = 0
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 12, p.18 (proof p.20)

import Mathlib
import Definitions.Def_LowDimMeanEst_ChernoffF

open MeasureTheory

namespace LowDimMeanEst

/-- **Lemma 12**, p.18 (proof p.20).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Consider the parameter δ ∈ (0, 1). Fix η > 0. Now consider a distribution D on ℝᵈ with mean µ and
second moment E[XX⊤] ⪯ (1 + γ)I for some γ ≥ 0. Let x₁, …, xₙ denote n i.i.d. samples drawn from D.
For any unit vector z ∈ ℝᵈ, dimension-d non-zero matrix A ⪰ 0, and parameters a, b, t ∈ ℝ, we have
that E_{x₁,…,xₙ←D}[e^{F(x,A,z,a,b,t)}] ≤ e^{r log(1/δ)}, where r is the objective value of the
following optimization problem, taking c = nTr(A)/log(1/δ):
min_{q₁,q₂≥0} (1 + γ)(q₁ + q₂) − a/3 − (1 + η)(t/√(n log(1/δ)))√2
s.t. 1 + (t/√(n log(1/δ))) x₂ + (q₁/c) x₁ + q₂x₂² ≥
e^{a+(−a+(bx₁−bcx₂²+(t/√(n log(1/δ)))x₂))(1−min(1,x₁))} ∀x₁ ≥ 0, x₂ ∈ ℝ. (15)"

**Formalization Note.**
* The bound is stated for **every** feasible `(q₁, q₂)` of (15), which gives the bound by the
  optimal value without assuming that the minimum is attained.
* The expectation is the lower Lebesgue integral of `e^F` (an `ℝ≥0∞` value), so it is not subject to
  the Bochner integral's junk value on non-integrable functions.
* `F` is Definition 10 with the fixed `η` and `µ = E[X]`. `n ≥ 1`: `n` is the number of samples.
* The hypothesis is on the uncentred second moment, as printed.
-/
theorem lemma_12 {d n : ℕ} (hn : 1 ≤ n) (δ η γ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hγ : 0 ≤ γ) (D : Measure (E d)) [IsProbabilityMeasure D] (hD : SecondMomentLe D (1 + γ))
    (z : E d) (hz : ‖z‖ = 1) (A : E d →L[ℝ] E d) (hA : A.IsPositive) (hA0 : A ≠ 0)
    (a b t q1 q2 : ℝ) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hfeas : ∀ x1 x2 : ℝ, 0 ≤ x1 →
      Real.exp (a + (-a + (b * x1 - b * ((n : ℝ) * tr A / logInv δ) * x2 ^ 2 +
          t / Real.sqrt (n * logInv δ) * x2)) * (1 - min 1 x1)) ≤
        1 + t / Real.sqrt (n * logInv δ) * x2 + q1 / ((n : ℝ) * tr A / logInv δ) * x1 +
          q2 * x2 ^ 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (chernoffF δ η (popMean D) x A z a b t))
        ∂(Measure.pi fun _ : Fin n => D) ≤
      ENNReal.ofReal (Real.exp (((1 + γ) * (q1 + q2) - a / 3 -
        (1 + η) * (t / Real.sqrt (n * logInv δ)) * Real.sqrt 2) * logInv δ)) := by sorry

end LowDimMeanEst
