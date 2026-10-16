-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_f_equivalence
-- name    : NeedPersuasion.FullInfo.f_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:48.164287+00:00
-- url     : https://prove2.me/theorems/608e1982-29c4-4b9a-a620-0818ebf73ac4
-- title:
--   App. C, proof of Proposition 3, p. 41 — W_L(m_fi) > W_L(m_fi − 1) iff f(λ_L, λ_H) < 0
-- statement:
--   Assume the standing assumptions. Then
--   $$W_L(m_{fi})>W_L(m_{fi}-1)\iff f(\lambda_L,\lambda_H)<0,$$
--   where
--   $$f(\lambda_L,\lambda_H)=\lambda_Lu_L(0)-\lambda_L\sum_{k=1}^{m_{fi}-1}(\lambda_H+\lambda_L)^k\big(u_L(k-1)-u_L(k)\big)-(1-\lambda_H)u_L(m_{fi}-1).$$
--
--   This turns the efficiency criterion of Theorem 4 into the sign of an explicit polynomial in $\lambda_L$, whose root is the threshold $\bar\Lambda_L(\lambda_H)$ of Proposition 3.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 3, p. 41

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model
import Definitions.Def_NeedPersuasion_FullInfo_Constants

namespace NeedPersuasion.FullInfo

theorem f_equivalence (M : Model) (hM : M.Standing) :
    WLx M ((mfi M : ℝ) - 1) < WLx M (mfi M) ↔ fF M < 0 := by sorry

end NeedPersuasion.FullInfo
