-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_proposition_1
-- name    : FrictionInvest.Benefit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:06.556986+00:00
-- url     : https://prove2.me/theorems/86878ce4-2fa5-4bd8-836a-874981912604
-- title:
--   Proposition 1, p. 93 — equilibrium production and loan face value
-- statement:
--   For a feasible borrowing firm with cost $c>0$, capital $y\ge0$, and $\gamma\in[0,1]$, a production quantity $q$ maximizes expected profit precisely when its marginal return equals marginal financing cost; its loan face value also satisfies the bank's zero-profit equation:
--   $$p(1-q/a)-c=\mathrm{MCE}(q),\qquad \mathbb E[\chi]=cq-y.$$
--   For an investing firm this specializes to equations (5) and (6) with $(c,y)=(c_2,y_2)$ and $q=q_A$. The same equations describe the noninvesting firm with $(c_1,y_1)$ and $q=q_0$.
--
--   **Formalization Note** The equivalence is stated on the feasible borrowing region, where the paper applies these marginal equations.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 93 (PDF 6), Proposition 1, equations (5)–(6)

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- Proposition 1, p. 93: the two equilibrium equations for a borrowing firm. -/
theorem proposition_1 (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y q : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1) (hc : 0 < c) (hy : 0 ≤ y)
    (hfeas : Feasible P γ c y q) (hborrow : y < c * q) :
    (IsEqQuantity P γ c y q ↔ mrr P c q = mce P γ c y q) ∧
    bankReceipt P γ q (faceValue P γ c y q) = c * q - y := by sorry

end FrictionInvest.Benefit
