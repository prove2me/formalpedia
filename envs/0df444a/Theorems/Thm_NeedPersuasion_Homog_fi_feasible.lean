-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_fi_feasible
-- name    : NeedPersuasion.Homog.fi_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:00.631833+00:00
-- url     : https://prove2.me/theorems/43170db4-c8eb-47ee-9f1e-dd91bb22842f
-- title:
--   App. C, proof of Proposition 1, p. 40 — with λ_H = 0, full information is a signaling mechanism and 0 < W_L(fi)
-- statement:
--   Consider the congested-service model under its standing assumptions in the homogeneous setting $\lambda_H = 0$. Let $\mathrm{fi} = \pi_{m_{fi}}$ be the full-information mechanism, under which L-users join exactly when the queue length $k$ has $u_L(k) \ge 0$. Then $\mathrm{fi}$ is a signaling mechanism and its L-welfare is positive:
--   $$\mathrm{fi} \in \Pi_{SM}, \qquad 0 < W_L(\mathrm{fi}).$$
--
--   Feasibility of $\mathrm{fi}$ is what makes $W_L(\mathrm{fi})$ a lower bound on the welfare of any optimal signaling mechanism.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 1, p. 40, first sentence

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model

namespace NeedPersuasion.Homog

theorem fi_feasible (M : Model) (hM : M.Standing) (hH : M.lamH = 0) :
    fi M ∈ PiSM M ∧ 0 < WL M (fi M) := by sorry

end NeedPersuasion.Homog
