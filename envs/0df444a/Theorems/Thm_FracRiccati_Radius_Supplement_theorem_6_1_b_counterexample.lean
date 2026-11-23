-- Prove2me | Theorems.Thm_FracRiccati_Radius_Supplement_theorem_6_1_b_counterexample
-- name    : FracRiccati.Radius.Supplement.theorem_6_1_b_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:57:38.541708+00:00
-- url     : https://prove2.me/theorems/a5501e4d-f00d-475e-b17b-9ff6f5383452
-- title:
--   Theorem 6.1(b) (corrected: counterexample to the valuation bound)
-- statement:
--   The printed valuation lower bound in case (b) is false. Take $\alpha=2$ and $\lambda=\mu=\nu=u=v=1$. For the coefficients constructed from its own recursion,
--   $$a_{1,4}=a_{2,4}=0,\qquad a_{3,4}=\frac12,\qquad k(4)=3<4.$$
--   Thus $k(4)\ge1+(4-1)$ fails even when all five complex parameters are nonzero, and without any Gamma pole. This counterexample refutes the conjunction asserted by Theorem 6.1(b); it does not substitute a restricted existence theorem for its solution assertion. The independent failure of integrability for $1<\alpha\le3/2$ with $\lambda v\ne0$ and possible repairs are recorded in DISPROOF.md.
--
--   Differences from the source:
--   - correction: case (b) asserts a solution with valuations at least l for l>=3 → a regular-input counterexample has valuation 3 at level 4; reason: the convolution includes a_(1,2)^2, yielding a_(3,4)=1/2 at alpha=2; see DISPROOF.md, item 3
--   - reading: coefficients below the claimed valuation are set to zero → the noncircular recurrence is applied to every row k>=2; reason: forcing a_(3,4)=0 would delete the nonzero t^0 term created by integrating the v^2 contribution, so the printed restriction cannot repair the equation
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 24, Theorem 6.1(b)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_DoubleSeries

namespace FracRiccati.Radius.Supplement

/-- At a regular Gamma input, the claimed valuation lower bound fails. -/
theorem theorem_6_1_b_counterexample :
    let a := doubleCoeff 2 1 1 1 1 1
    a 1 4 = 0 ∧ a 2 4 = 0 ∧ a 3 4 = (1 / 2 : ℂ) ∧
    valuation a 4 = (3 : ℕ∞) ∧
    ¬ ((1 + (4 - 1) : ℕ) : ℕ∞) ≤ valuation a 4 := by sorry

end FracRiccati.Radius.Supplement
