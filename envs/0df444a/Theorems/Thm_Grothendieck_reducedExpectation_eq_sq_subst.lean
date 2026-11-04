-- Prove2me | Theorems.Thm_Grothendieck_reducedExpectation_eq_sq_subst
-- name    : Grothendieck.reducedExpectation_eq_sq_subst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:32:34.500193+00:00
-- url     : https://prove2.me/theorems/7186e839-dfaa-4176-be28-cbae23d9a235
-- title:
--   Step 4b of Lemma 2.1: the substitutions $s=u^2/2$, $t=v^2/2$
-- statement:
--   With $X,Y$ the two columns of a random $r\times2$ matrix whose rows are bivariate Gaussians of correlation $\tau$, $r\ge2$, $|\tau|<1$,
--
--   $$
--   \int_W \mathrm{reducedIntegrand}_r(W)\,d(\texttt{reducedLaw}\,r\,\tau)
--   =\frac{2r\tau}{\pi}\int_{(0,\infty)^2}\Big((1+u^2)(1+v^2)-\tau^2u^2v^2\Big)^{-\frac{r+2}{2}}\,du\,dv .
--   $$
--   This is the substitution $s=u^2/2$, $t=v^2/2$ in the Laplace parameters of Lemma 2.1. It removes the singular factor: $(st)^{-1/2}\,ds\,dt=2\,du\,dv$, so the kernel form's $(st)^{-1/2}\big((1+2s)(1+2t)-4\tau^2st\big)^{-(r+2)/2}$ becomes $2\big((1+u^2)(1+v^2)-\tau^2u^2v^2\big)^{-(r+2)/2}$.
--
--   The one-dimensional content is published as `Grothendieck.integral_sqrt_inv_mul_eq`: the measure with density $(2s)^{-1/2}$ on $(0,\infty)$ is the pushforward of Lebesgue measure under $u\mapsto u^2/2$. What this node adds is the two-variable assembly, which requires iterating the product-measure integral (and hence integrability of the kernel).
--
--   After this substitution the remaining steps are one-variable calculus: the $u$-integral is the published `Grothendieck.integral_add_mul_sq_rpow_neg` at $A=1+v^2$, $B=1+(1-\tau^2)v^2$, and the $v$-integral is the published `Grothendieck.integral_sq_subst`, which lands on the Beta integral of `Grothendieck.Er_eq_betaIntegral`.
--
--   **Formalization Note** The statement is verified to elaborate; the proof is open.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - the substitutions s=p^2/2, t=q^2/2 in the proof of Lemma 2.1.

import Mathlib
import Definitions.Def_Grothendieck_Reduced
import Definitions.Def_Grothendieck_Fubini

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **Step 4b: the substitutions `s = p²/2`, `t = q²/2`.** -/
theorem reducedExpectation_eq_sq_subst (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = 2 * (r : ℝ) * τ * Real.pi⁻¹ * ∫ p,
          (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure := by sorry

end Grothendieck
