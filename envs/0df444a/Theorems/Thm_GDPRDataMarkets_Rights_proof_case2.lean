-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_proof_case2
-- name    : GDPRDataMarkets.Rights.proof_case2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:29.19189+00:00
-- url     : https://prove2.me/theorems/fa2a9c6a-5860-4279-bd43-bb31e282e51d
-- title:
--   Appendix, proof of Proposition 1, case 2, p. 47 — for δσ/2 < c < δσ/√2, p₁ = 1/2 maximizes the reduced profit
-- statement:
--   Assume the standing assumptions, Assumption 1, and
--   $$\frac{\delta\sigma}{2}\ <\ c\ <\ \frac{\delta\sigma}{\sqrt2}.$$
--   Then $p_1=1/2$ maximizes the reduced first-period profit $\pi(p_1)$ over all real $p_1$, and
--   $$\frac1{\sqrt2}\ >\ v^*_M(1/2)=\frac{c}{\delta\sigma}\ >\ \frac12.$$
--
--   By eq. (3) the equilibrium basic price is then $p^*_{2M}=1$ (no basic good is sold): this is case B of Proposition 1.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 47, Appendix, proof of Proposition 1, case 2

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- Appendix, proof of Proposition 1, case 2, p. 47: if `δσ/2 < c < δσ/√2`, then `p₁ = 1/2` maximizes
the reduced first-period profit over all real `p₁`, and `1/√2 > v*_M(1/2) = c/(δσ) > 1/2`. -/
theorem proof_case2 (P : Params) (hS : P.Standing) (hA : P.Assumption1)
    (hc : P.d * P.sigma / 2 < P.c ∧ P.c < P.d * P.sigma / Real.sqrt 2) :
    (∀ p1 : ℝ, profitRed P p1 ≤ profitRed P (1 / 2)) ∧
    vStar P (1 / 2) = P.c / (P.d * P.sigma) ∧
    vStar P (1 / 2) < 1 / Real.sqrt 2 ∧ 1 / 2 < vStar P (1 / 2) := by sorry

end GDPRDataMarkets.Rights
