-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_proposition_4
-- name    : FrictionInvest.Benefit.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:04.522138+00:00
-- url     : https://prove2.me/theorems/ea5894ec-0337-4fde-a36c-efe04125747d
-- title:
--   Proposition 4, p. 95 — a positive friction effect increases investment benefit
-- statement:
--   Let the firm's cost-reduction investment lower unit cost from $c_1$ to $c_2=c_1-\beta A>0$, and let $\gamma\in(0,1]$. At each friction level, compare expected profits at feasible maximizing production quantities before and after investing. If the friction effect $\Delta R_2(\gamma)$ of equation (8) is positive, then
--   $$\Pi(\gamma)>\Pi(0).$$
--   Thus the investment's net benefit is greater with capital market frictions than in their absence.
--
--   **Formalization Note** The statement adds $c_1<p$ because the printed integral (8) gives a false implication when its first upper limit becomes negative. Self-financed quantities use $\mathrm{MCE}=0$. The paper's usual insufficient-capital assumption is omitted; the claimed implication also covers self-financed cases.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 95 (PDF 8), Proposition 4

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- Proposition 4, p. 95: a positive friction effect raises investment's net benefit. -/
theorem proposition_4 (P : Params) (hS : P.Standing) (hcp : P.c1 < P.p)
    (γ : ℝ) (hγ : 0 < γ ∧ γ ≤ 1)
    (q0 qA : ℝ) (h0 : IsEqQuantity P γ P.c1 P.y1 q0)
    (hA : IsEqQuantity P γ P.c2 P.y2 qA)
    (q0' qA' : ℝ) (h0' : IsEqQuantity P 0 P.c1 P.y1 q0')
    (hA' : IsEqQuantity P 0 P.c2 P.y2 qA') :
    0 < frictionEffect P γ q0 qA →
      netBenefit P 0 q0' qA' < netBenefit P γ q0 qA := by sorry

end FrictionInvest.Benefit
