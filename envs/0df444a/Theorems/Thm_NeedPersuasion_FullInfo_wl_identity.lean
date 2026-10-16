-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_wl_identity
-- name    : NeedPersuasion.FullInfo.wl_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:59.684018+00:00
-- url     : https://prove2.me/theorems/ce5ec42f-5e8c-4eac-901e-308033f7c0eb
-- title:
--   App. C, proof of Proposition 3, pp. 41–42 — the identity for W_L(m − 1) in terms of W_L(m) and u_L(m − 1), for 1 ≤ m ≤ m_fi
-- statement:
--   Assume the standing assumptions and $\lambda<1$, and let $1\le m\le m_{fi}$. Then the L welfare of the threshold policies with thresholds $m-1$ and $m$ satisfy
--   $$W_L(m-1)=\Big(1+\frac{(1-\lambda)\lambda_L\lambda^{m-1}}{1-\lambda_H-\lambda_L\lambda^{m-1}}\Big)W_L(m)-\Big(\frac{(1-\lambda_H)(1-\lambda)\lambda_L\lambda^{m-1}}{1-\lambda_H-\lambda_L\lambda^{m-1}}\Big)u_L(m-1).$$
--
--   At $m=m_{fi}$ this identity produces the factor $\beta_{L,sm}$ of Proposition 3(2).
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 3, pp. 41–42

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem wl_identity (M : Model) (hM : M.Standing) (hlt : M.lam < 1) (m : ℕ)
    (hm1 : 1 ≤ m) (hm : m ≤ mfi M) :
    WLx M ((m : ℝ) - 1) =
      (1 + (1 - M.lam) * M.lamL * M.lam ^ (m - 1) / (1 - M.lamH - M.lamL * M.lam ^ (m - 1))) *
          WLx M m -
        ((1 - M.lamH) * (1 - M.lam) * M.lamL * M.lam ^ (m - 1) /
            (1 - M.lamH - M.lamL * M.lam ^ (m - 1))) * M.uL (m - 1) := by sorry

end NeedPersuasion.FullInfo
