-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_proposition_3_decomposition
-- name    : FrictionInvest.Benefit.proposition_3_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:01.180265+00:00
-- url     : https://prove2.me/theorems/f550185e-e8ef-40b4-b440-6e43a491d589
-- title:
--   Proposition 3, p. 95 — net benefit decomposes into operational and friction effects
-- statement:
--   Let $q_0,q_A$ be equilibrium quantities under a common friction proportion $\gamma\in[0,1]$, and let $q_0^{\mathrm p},q_A^{\mathrm p}$ be their perfect-market counterparts. With $\Delta R_2$ defined by equation (8), the investment's net benefit decomposes as
--   $$\Pi(\gamma)=\Delta R_1+\Delta R_2(\gamma)-A.$$
--   Here $\Delta R_1$ compares perfect-market operating profits and $\Delta R_2$ is the four-integral change in financing costs. This identity connects the paper's area analysis to its investment decision.
--
--   **Formalization Note** The statement formalizes Proposition 3's formula (8) and the displayed decomposition at the opening of p. 95. Its later threshold claim about $\hat\beta$ is outside this mission.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 95 (PDF 8), Proposition 3, equation (8), and the opening decomposition

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- Proposition 3 and the opening decomposition on p. 95, with `ΔR₂` given by (8). -/
theorem proposition_3_decomposition (P : Params) (hS : P.Standing)
    (hcp : P.c1 < P.p) (γ : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1)
    (q0 qA : ℝ) (h0 : IsEqQuantity P γ P.c1 P.y1 q0)
    (hA : IsEqQuantity P γ P.c2 P.y2 qA)
    (q0' qA' : ℝ) (h0' : IsEqQuantity P 0 P.c1 P.y1 q0')
    (hA' : IsEqQuantity P 0 P.c2 P.y2 qA') :
    netBenefit P γ q0 qA =
      opEffect P q0' qA' + frictionEffect P γ q0 qA - P.A := by sorry

end FrictionInvest.Benefit
