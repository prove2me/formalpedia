-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_obedient_threshold_ge
-- name    : NeedPersuasion.Homog.obedient_threshold_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:57.614002+00:00
-- url     : https://prove2.me/theorems/ea74e735-19b6-41b0-aa7e-7642e7a1753e
-- title:
--   App. C, proof of Proposition 1, p. 40 — with λ_H = 0, every obedient threshold policy has threshold ≥ m_fi − 1
-- statement:
--   Consider the congested-service model under its standing assumptions in the homogeneous setting $\lambda_H = 0$. Let $x \ge 0$ and suppose the threshold policy $\pi_x$ is a signaling mechanism, i.e. it satisfies the obedience constraints (JOIN) and (LEAVE). Then
--   $$x \ge m_{fi} - 1 .$$
--
--   Together with Theorem 1 this places the threshold of the optimal signaling mechanism in the interval $[m_{fi} - 1, m_{fi}]$.
--
--   **Formalization Note** The page argues for the threshold $x_{sm}$ of the optimal mechanism; the statement is posed for every obedient threshold policy, which is what the argument uses. Since $u_L(0) > 0$, $m_{fi} \ge 1$.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 1, p. 40

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model

namespace NeedPersuasion.Homog

theorem obedient_threshold_ge (M : Model) (hM : M.Standing) (hH : M.lamH = 0)
    (x : ℝ) (hx : 0 ≤ x) (hobed : thresholdPolicy M x ∈ PiSM M) :
    (mfi M : ℝ) - 1 ≤ x := by sorry

end NeedPersuasion.Homog
