-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_no_both_unbounded
-- name    : OAI.BackwardIntertwiners.no_both_unbounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:20:24.397003+00:00
-- url     : https://prove2.me/theorems/ab29a318-3b6f-4030-82b2-72b4c042d187
-- title:
--   Vanishing positive-lag correlations exclude coefficients unbounded in both directions under quadratic convex profiles
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. Let $P,Q:\mathbb{N}\to\mathbb{R}$ be discretely convex with $P(0)=Q(0)=0$, and let $b,c:\mathbb{Z}\to\mathbb{C}$ satisfy, for every $n\in\mathbb{N}$,
--   $$|b(n)|\le e^{-Q(n)},\qquad|b(-n)|\le e^{P(n)},\qquad|c(n)|\le e^{Q(n)},\qquad|c(-n)|\le e^{-P(n)}.$$
--   Let $\lambda,\delta\in\mathbb{R}$ with $\log3<\lambda<\delta$, and suppose $P(n)\ge\delta n^2$ and $Q(n)\ge\delta n^2$ for all sufficiently large $n$. Assume that $b$ has nonzero entries at arbitrarily large positive indices and $c$ at arbitrarily large negative indices: for every $n\in\mathbb{N}$ there are $k,k'\in\mathbb{N}$ with $k>n$, $k'>n$, $b(k)\neq0$ and $c(-k')\neq0$.
--
--   Then it is impossible that
--   $$\sum_{j\in\mathbb{Z}}b(j)\,c(j-r)=0\qquad\text{for every integer }r\ge1.$$
--
--   In the project's support separation argument this rules out the case in which the support of $b$ is unbounded above and the support of $c$ is unbounded below simultaneously. Unlike the general correlation obstruction, no contact conditions are assumed: the profiles $P,Q$ are arbitrary convex profiles of quadratic growth.
--
--   **Formalization Note** The four inequalities are `EnvelopeBounds P Q b c`, and the conclusion is `False`. The correlations are Mathlib's unconditional sums `tsum`, which are $0$ for non-summable families, so the hypothesis that they vanish is no stronger than requiring the series to converge to $0$. The hypotheses on $\lambda$ amount to $\delta>\log3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean#L70-L93

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.no_both_unbounded {P Q : ℕ → ℝ} {b c : ℤ → ℂ}
    (hb : EnvelopeBounds P Q b c) (hP : DiscreteConvex P) (hQ : DiscreteConvex Q)
    (hP0 : P 0 = 0) (hQ0 : Q 0 = 0) {lam δ : ℝ}
    (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^2 ≤ P n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^2 ≤ Q n)
    (hbu : ∀ n : ℕ, ∃ k, n < k ∧ b (k : ℤ) ≠ 0)
    (hcu : ∀ n : ℕ, ∃ k, n < k ∧ c (-(k : ℤ)) ≠ 0)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by sorry
