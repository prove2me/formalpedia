-- Prove2me | Theorems.Thm_Grothendieck_reducedExpectation_eq_kernel
-- name    : Grothendieck.reducedExpectation_eq_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:49.807199+00:00
-- url     : https://prove2.me/theorems/79ebca96-cd31-44f7-8810-c350deea6fcf
-- title:
--   The rounding expectation in kernel form: a two-dimensional elementary integral
-- statement:
--   With $X,Y$ the two columns of a random $r\times2$ matrix whose rows are bivariate Gaussians of correlation $\tau$, and $r\ge2$, $|\tau|<1$,
--
--   $$
--   \int_W \mathrm{reducedIntegrand}_r(W)\,d(\texttt{reducedLaw}\,r\,\tau)
--   =\frac{r\tau}{\pi}\int_{(0,\infty)^2}(st)^{-1/2}\Big((1+2s)(1+2t)-4\tau^2st\Big)^{-\frac{r+2}{2}}\,ds\,dt .
--   $$
--
--   This is the whole Gaussian content of Lemma 2.1 reduced to a **two-dimensional elementary integral**: after the Fubini swap the inner integral over $W$ is the row-wise Gaussian integral, which evaluates in closed form to $r\tau C^{r+2}$ with $C=\big((1+2s)(1+2t)-4\tau^2st\big)^{-1/2}$.
--
--   Everything left in the lemma is now one-variable calculus on the right-hand side: the substitution $s=p^2/2$, $t=q^2/2$ turns the integrand into $((1+p^2)(1+q^2)-\tau^2p^2q^2)^{-(r+2)/2}$, the $p$-integral is the standard Beta integral, and $q^2=x/(1-x)$ lands on $\int_0^1x^{-1/2}(1-x)^{(r-1)/2}(1-\tau^2x)^{-1/2}dx$ — the published `Grothendieck.Er_eq_betaIntegral`.
--
--   **Formalization Note** Uses `Grothendieck.fubini_swap` and `Grothendieck.integral_reducedLaw_row`; the inner-product and norm identities relating the two columns of $W$ to sums over the rows are proved in the submitted file.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 2.1 and its proof, pp. 84-87.

import Mathlib
import Definitions.Def_Grothendieck_Reduced
import Definitions.Def_Grothendieck_Fubini

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The kernel form of the rounding expectation.** The expectation is `π⁻¹ r τ` times the integral
of the Laplace kernel `(st)^{-1/2} C^{r+2}` over the positive quadrant. -/
theorem reducedExpectation_eq_kernel (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, ((p.1 * p.2) ^ (-(1/2) : ℝ) *
          ((r : ℝ) * τ *
            ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-(((r : ℝ) + 2) / 2) : ℝ)))
          ∂planeMeasure := by sorry

end Grothendieck
