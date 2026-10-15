-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_proof_case3
-- name    : GDPRDataMarkets.Rights.proof_case3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:02.603178+00:00
-- url     : https://prove2.me/theorems/7c9f518f-0b93-43c3-b839-7a8d2b312d24
-- title:
--   Appendix, proof of Proposition 1, case 3, pp. 47–48 — for c ≤ δσ/2, p₁ = P₁* maximizes the reduced profit and v*_M(P₁*) = v₁*
-- statement:
--   Assume the standing assumptions, Assumption 1, and $c\le\delta\sigma/2$. Then $p_1=P_1^*$ maximizes the reduced first-period profit $\pi(p_1)$ over all real $p_1$,
--   $$v^*_M(P_1^*)=v_1^*,\qquad v_1^*<\frac1{\sqrt2},$$
--   where
--   $$v_1^*=\max\Big\{\frac{1+\delta\sigma+(1+\delta)c}{2+\delta+\delta\mu+\delta\sigma},\frac{c}{\delta\sigma}\Big\},\qquad P_1^*=\max\Big\{\frac{(1+\delta\sigma)^2-(1+\delta\mu-\delta^2\sigma)c}{2+\delta+\delta\mu+\delta\sigma},\frac{c}{\delta\sigma}\Big\}.$$
--
--   The last inequality gives, by eq. (3), the equilibrium basic price $p^*_{2M}=1$: this is case A of Proposition 1.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), pp. 47–48, Appendix, proof of Proposition 1, case 3; p. 46, definitions of v₁*, P₁*

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- Appendix, proof of Proposition 1, case 3, p. 48: if `c ≤ δσ/2`, then `p₁ = P₁*` maximizes the
reduced first-period profit over all real `p₁`, `v*_M(P₁*) = v₁*`, and `v₁* < 1/√2` (so that
`p*_2M = 1` by eq. (3)). -/
theorem proof_case3 (P : Params) (hS : P.Standing) (hA : P.Assumption1)
    (hc : P.c ≤ P.d * P.sigma / 2) :
    (∀ p1 : ℝ, profitRed P p1 ≤ profitRed P (P1star P)) ∧
    vStar P (P1star P) = v1star P ∧ v1star P < 1 / Real.sqrt 2 := by sorry

end GDPRDataMarkets.Rights
