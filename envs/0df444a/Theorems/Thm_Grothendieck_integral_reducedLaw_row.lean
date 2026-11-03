-- Prove2me | Theorems.Thm_Grothendieck_integral_reducedLaw_row
-- name    : Grothendieck.integral_reducedLaw_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:27:33.866273+00:00
-- url     : https://prove2.me/theorems/a993c35e-20ed-4a86-9852-79fcd37d0250
-- title:
--   The row-wise Gaussian integral of Lemma 2.1, with the correct constant
-- statement:
--   Let $W_1,\dots,W_r$ be independent bivariate Gaussians with mean $0$ and covariance $\big(\begin{smallmatrix}1&\tau\\\tau&1\end{smallmatrix}\big)$, $|\tau|<1$, and let $a,b>0$. Then
--
--   $$
--   \int \Big(\sum_{i}W_{i0}W_{i1}\Big)\exp\Big(-a\sum_i W_{i0}^2-b\sum_i W_{i1}^2\Big)d(\text{law})=r\,\tau\,C^{r+2},
--   \qquad C=\big((1+2a)(1+2b)-4\tau^2ab\big)^{-1/2}.
--   $$
--
--   This is Steps 1 and 2 of the proof of Lemma 2.1: the rows are independent, so the expectation factorizes into one row carrying the numerator and the others carrying the exponential; each factor is an explicit two-dimensional Gaussian integral.
--
--   $$
--   C=E\big[e^{-(a\xi^2+b\eta^2)}\big]=\big(\sigma^2\det M\big)^{-1/2},\qquad A=E\big[\xi\eta\,e^{-(a\xi^2+b\eta^2)}\big]=\tau\alpha\sigma^2C^3=\tau C^3,
--   $$
--
--   with $\alpha=1/\sigma^2$, $\sigma^2=1-\tau^2$ and $M=M_0+2\,\mathrm{diag}(a,b)$; hence the integral is $r\cdot A\cdot C^{r-1}=r\tau C^{r+2}$.
--
--   **A note on the constant.** The paper writes $A=2\tau C^3$. That is a factor two too large: at $a=b=0$ it gives $A=2\tau$ while $E[\xi\eta]=\tau$, and numerically the row integral equals $r\tau C^{r+2}$ (Monte Carlo agrees to four digits on four parameter sets) rather than $2r\tau C^{r+2}$. The paper's slip does not affect its final identity, since the constant is carried along consistently once fixed; the node records the value that is correct.
--
--   **Formalization Note** The measure is `Grothendieck.reducedLaw r τ` of the definition layer, i.e. $r$ independent copies of that bivariate Gaussian. This is step (i) of the last missing half of Lemma 2.1.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — steps 1-2 of the proof of Lemma 2.1, pp. 85-87. The paper's display $A=2\tau C^3$ is corrected to $A=\tau C^3$; see the statement.

import Mathlib
import Definitions.Def_Grothendieck_Reduced

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The row-wise Gaussian integral (Step 1-2 of Lemma 2.1).** For `r` independent bivariate
Gaussians of correlation `τ` and `a, b > 0`,

`∫ W, (Σᵢ Wᵢ₀Wᵢ₁)·exp(-(a Σᵢ Wᵢ₀² + b Σᵢ Wᵢ₁²)) = r·τ·((1+2a)(1+2b) - 4τ²ab)^{-(r+2)/2}`.

The constant is `r·τ·C^(r+2)` with `C = ((1+2a)(1+2b) - 4τ²ab)^{-1/2}`; note that this is *not*
`2rτC^(r+2)`, see the node's discussion of the paper's `A = 2τC³`. -/
theorem integral_reducedLaw_row {r : ℕ} {tau a b : ℝ} (ha : 0 < a) (hb : 0 < b) (htau : tau ^ 2 < 1) :
    (∫ W : Fin r → EuclideanSpace ℝ (Fin 2),
        (∑ i, (W i).ofLp 0 * (W i).ofLp 1) *
          Real.exp (-(a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2))
        ∂(reducedLaw r tau))
      = r * tau * ((1 + 2 * a) * (1 + 2 * b) - 4 * tau ^ 2 * a * b) ^ (-(((r : ℝ) + 2) / 2) : ℝ) := by sorry

end Grothendieck
