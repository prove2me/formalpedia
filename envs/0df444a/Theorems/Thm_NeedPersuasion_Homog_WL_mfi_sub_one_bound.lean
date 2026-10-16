-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_WL_mfi_sub_one_bound
-- name    : NeedPersuasion.Homog.WL_mfi_sub_one_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:55.76461+00:00
-- url     : https://prove2.me/theorems/36470752-a178-4b8c-b497-fa5ba496cb85
-- title:
--   App. C, proof of Proposition 1, p. 40 — with λ_H = 0, β_fi · W_L(m_fi − 1) ≤ W_L(fi)
-- statement:
--   Consider the congested-service model under its standing assumptions in the homogeneous setting $\lambda_H = 0$, with full-information threshold $m_{fi}$ and
--   $$\beta_{fi} = \frac{\sum_{n=0}^{m_{fi}-1}\lambda_L^n}{\sum_{n=0}^{m_{fi}}\lambda_L^n}.$$
--   Let $W_L(m_{fi}-1)$ be the L-welfare of the threshold policy with threshold $m_{fi} - 1$, and $W_L(\mathrm{fi})$ that of the full-information mechanism. Then
--   $$\beta_{fi}\, W_L(m_{fi} - 1) \le W_L(\mathrm{fi}).$$
--
--   This is the inequality $W_L(m_{fi}-1) \le \beta_{fi}^{-1} W_L(\mathrm{fi})$ of the proof of Proposition 1.
--
--   **Formalization Note** Both welfares are computed from the threshold distributions. The page's display omits the common factor $\lambda_L$ of both welfares, which does not affect the inequality.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 1, p. 40 (display)

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model
import Definitions.Def_NeedPersuasion_Homog_BetaFi

namespace NeedPersuasion.Homog

theorem WL_mfi_sub_one_bound (M : Model) (hM : M.Standing) (hH : M.lamH = 0) :
    betaFi M * WLx M ((mfi M : ℝ) - 1) ≤ WL M (fi M) := by sorry

end NeedPersuasion.Homog
