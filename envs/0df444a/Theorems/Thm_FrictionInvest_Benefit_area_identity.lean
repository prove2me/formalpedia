-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_area_identity
-- name    : FrictionInvest.Benefit.area_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:01.227686+00:00
-- url     : https://prove2.me/theorems/5e42ecb0-d255-42fa-8f9d-228e1472be6f
-- title:
--   §3.2, p. 94 — expected profit as an area between marginal curves
-- statement:
--   For unit cost $0<c<p$, capital $y\ge0$, and $\gamma\in[0,1]$, let $q$ maximize expected production profit under friction and let $q^{\mathrm p}$ maximize it at $\gamma=0$. Put $q_c^{\mathrm p}=a(p-c)/p$. Then
--   $$J_0(c,y,q^{\mathrm p})=\int_0^{q_c^{\mathrm p}}\mathrm{MRR}(t)\,dt,$$
--   and
--   $$J_\gamma(c,y,q)=\int_0^{q_c^{\mathrm p}}\mathrm{MRR}(t)\,dt-\left(\int_q^{q_c^{\mathrm p}}\mathrm{MRR}(t)\,dt+\int_0^q\mathrm{MCE}(t)\,dt\right).$$
--   These are the operational-profit area and the cost-of-external-funds area of Figure 2. The investing firm's net profit is obtained by subtracting $A$ once.
--
--   **Formalization Note** The two area identities use the profit defined by the revenue and bankruptcy-cost expectations, rather than defining profit as an area.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 94 (PDF 7), §3.2, Figure 2 and the unnumbered area identities

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- §3.2, p. 94: operating profit is the area below MRR less the financing-cost area. -/
theorem area_identity (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y q qperfect : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1)
    (hc : 0 < c ∧ c < P.p) (hy : 0 ≤ y)
    (heq : IsEqQuantity P γ c y q)
    (hperfect : IsEqQuantity P 0 c y qperfect) :
    expProfit P 0 c y qperfect =
      ∫ t in (0)..(P.a * (P.p - c) / P.p), mrr P c t ∧
    expProfit P γ c y q =
      (∫ t in (0)..(P.a * (P.p - c) / P.p), mrr P c t) -
      ((∫ t in q..(P.a * (P.p - c) / P.p), mrr P c t) +
        (∫ t in (0)..q, mce P γ c y t)) := by sorry

end FrictionInvest.Benefit
