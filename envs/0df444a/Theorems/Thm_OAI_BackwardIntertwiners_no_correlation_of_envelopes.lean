-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_no_correlation_of_envelopes
-- name    : OAI.BackwardIntertwiners.no_correlation_of_envelopes
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:19:13.415385+00:00
-- url     : https://prove2.me/theorems/2449e9f7-a04e-44d5-9d4a-df0427fee70d
-- title:
--   Sequences under quadratically growing convex envelopes cannot have all positive-lag correlations vanishing
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. For $A,B:\mathbb{N}\to\mathbb{R}$ and $b,c:\mathbb{Z}\to\mathbb{C}$, say that $(b,c)$ satisfies the *envelope bounds with profiles* $(A,B)$ if for every $n\in\mathbb{N}$
--   $$|b(n)|\le e^{-B(n)},\qquad|b(-n)|\le e^{A(n)},\qquad|c(n)|\le e^{B(n)},\qquad|c(-n)|\le e^{-A(n)}.$$
--
--   Let $A,B:\mathbb{N}\to\mathbb{R}$ be discretely convex with $A(0)=B(0)=0$, and let $b,c:\mathbb{Z}\to\mathbb{C}$ satisfy the envelope bounds with profiles $(A,B)$. Let $\lambda,\delta\in\mathbb{R}$ with $\log3<\lambda<\delta$, and suppose $A(n)\ge\delta n^2$ and $B(n)\ge\delta n^2$ for all sufficiently large $n$. Assume the contact conditions: for every $n\in\mathbb{N}$,
--   $$\Delta^2A(n)>0\implies|c(-(n+1))|=e^{-A(n+1)},\qquad\Delta^2B(n)>0\implies|b(n+1)|=e^{-B(n+1)}.$$
--   Then it is impossible that
--   $$\sum_{j\in\mathbb{Z}}b(j)\,c(j-r)=0\qquad\text{for every integer }r\ge1.$$
--
--   This is the core analytic obstruction behind the project's support separation for quadratically decaying weights. The contact conditions are exactly what convex envelopes of coefficient sequences provide, so the theorem applies to pairs whose coefficients are dominated by quadratically growing convex profiles, with $b$ decaying to the right and $c$ decaying to the left.
--
--   **Formalization Note** The envelope bounds are `EnvelopeBounds A B b c` and the conclusion is `False`. The correlations are Mathlib's unconditional sums `tsum`, which are $0$ for non-summable families, so the hypothesis that they vanish is no stronger than requiring the series to converge to $0$. Since $\lambda$ enters only through $\log3<\lambda<\delta$, the hypotheses on $\lambda$ amount to $\delta>\log3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvolutionBounds.lean#L238-L314

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.no_correlation_of_envelopes {A B : ℕ → ℝ} {b c : ℤ → ℂ}
    (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    {lam δ : ℝ} (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqa : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ A n)
    (hqb : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ B n)
    (hcA : ∀ n, 0 < A (n+2) - 2*A (n+1) + A n →
      ‖c (-((n+1 : ℕ) : ℤ))‖ = Real.exp (-A (n+1)))
    (hcB : ∀ n, 0 < B (n+2) - 2*B (n+1) + B n →
      ‖b ((n+1 : ℕ) : ℤ)‖ = Real.exp (-B (n+1)))
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by sorry
