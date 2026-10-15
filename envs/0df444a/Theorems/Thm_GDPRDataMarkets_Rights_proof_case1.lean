-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_proof_case1
-- name    : GDPRDataMarkets.Rights.proof_case1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:02.476819+00:00
-- url     : https://prove2.me/theorems/b41712ab-6295-4859-a74a-04dd4fc93a3f
-- title:
--   Appendix, proof of Proposition 1, case 1, p. 47 — for δσ/√2 ≤ c < δσ, p₁ = 1/2 maximizes the reduced profit
-- statement:
--   Assume the standing assumptions, Assumption 1, and
--   $$\frac{\delta\sigma}{\sqrt2}\ \le\ c\ <\ \deltas.$$
--   Then $p_1=1/2$ maximizes the reduced first-period profit $\pi(p_1)$ over all real $p_1$, and
--   $$1\ >\ v^*_M(1/2)=\frac{c}{\delta\sigma}\ \ge\ \frac1{\sqrt2}.$$
--
--   By eq. (3) the equilibrium basic price is then $p^*_{2M}=1/2$: this is case C of Proposition 1 (and the knife-edge $c=\delta\sigma/\sqrt2$).
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 47, Appendix, proof of Proposition 1, case 1

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- Appendix, proof of Proposition 1, case 1, p. 47: if `δσ/√2 ≤ c < δσ`, then `p₁ = 1/2` maximizes
the reduced first-period profit over all real `p₁`, and `1 > v*_M(1/2) = c/(δσ) ≥ 1/√2`. -/
theorem proof_case1 (P : Params) (hS : P.Standing) (hA : P.Assumption1)
    (hc : P.d * P.sigma / Real.sqrt 2 ≤ P.c ∧ P.c < P.d * P.sigma) :
    (∀ p1 : ℝ, profitRed P p1 ≤ profitRed P (1 / 2)) ∧
    vStar P (1 / 2) = P.c / (P.d * P.sigma) ∧
    vStar P (1 / 2) < 1 ∧ 1 / Real.sqrt 2 ≤ vStar P (1 / 2) := by sorry

end GDPRDataMarkets.Rights
