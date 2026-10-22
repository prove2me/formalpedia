-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_proposition_2
-- name    : FrictionInvest.Benefit.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:02.615521+00:00
-- url     : https://prove2.me/theorems/8ced45b6-0192-4296-ad90-c5054062cd08
-- title:
--   Proposition 2, p. 95 — positive operational effect
-- statement:
--   Let $q_0^{\mathrm p}$ and $q_A^{\mathrm p}$ be profit-maximizing production quantities without capital market frictions, before and after an investment $A>0$. With $c_2=c_1-\beta A>0$ and $c_1<p$, the operational effect is positive and equals
--   $$\Delta R_1=\frac{a\beta A(2p-2c_1+\beta A)}{2p}>0.$$
--   This is the part of the investment benefit independent of the friction proportion $\gamma$.
--
--   **Formalization Note** The explicit $c_1<p$ restriction is needed for the displayed formula; without it the perfect-market optimum may be zero.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 95 (PDF 8), Proposition 2

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- Proposition 2, p. 95: the positive operational effect and its closed form. -/
theorem proposition_2 (P : Params) (hS : P.Standing) (hcp : P.c1 < P.p)
    (q0' qA' : ℝ) (h0' : IsEqQuantity P 0 P.c1 P.y1 q0')
    (hA' : IsEqQuantity P 0 P.c2 P.y2 qA') :
    opEffect P q0' qA' =
      P.a * P.β * P.A * (2 * P.p - 2 * P.c1 + P.β * P.A) / (2 * P.p) ∧
    0 < opEffect P q0' qA' := by sorry

end FrictionInvest.Benefit
