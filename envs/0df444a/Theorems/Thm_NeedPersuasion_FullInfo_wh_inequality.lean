-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_wh_inequality
-- name    : NeedPersuasion.FullInfo.wh_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:04.560469+00:00
-- url     : https://prove2.me/theorems/2ac404cc-8eee-417b-9efd-b1c04c123686
-- title:
--   App. C, proof of Proposition 3, p. 42 — the lower bound on W_H(m − 1) in terms of W_H(m) and u_H(m), for 1 ≤ m ≤ m_fi
-- statement:
--   Assume the standing assumptions, $\lambda<1$, and that $\sum_n\lambda_H^nu_H(n)$ converges, and let $1\le m\le m_{fi}$. Then
--   $$W_H(m-1)\ge\Big(1+\frac{(1-\lambda)\lambda_L\lambda^{m-1}}{1-\lambda_H-\lambda_L\lambda^{m-1}}\Big)W_H(m)-\Big(\frac{\lambda_H(1-\lambda)\lambda_L\lambda^{m-1}}{1-\lambda_H-\lambda_L\lambda^{m-1}}\Big)u_H(m).$$
--
--   At $m=m_{fi}$ this inequality produces the factor $\beta_{H,sm}$ of Proposition 3(2).
--
--   **Formalization Note** The summability hypothesis is the finite-welfare convention: it makes $W_H(m)$ and $W_H(m-1)$ genuine (finite) sums.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 3, p. 42

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem wh_inequality (M : Model) (hM : M.Standing) (hlt : M.lam < 1)
    (hFin : Summable (fun n : ℕ => M.lamH ^ n * M.uH n)) (m : ℕ)
    (hm1 : 1 ≤ m) (hm : m ≤ mfi M) :
    (1 + (1 - M.lam) * M.lamL * M.lam ^ (m - 1) / (1 - M.lamH - M.lamL * M.lam ^ (m - 1))) *
          WHx M m -
        (M.lamH * (1 - M.lam) * M.lamL * M.lam ^ (m - 1) /
            (1 - M.lamH - M.lamL * M.lam ^ (m - 1))) * M.uH m ≤
      WHx M ((m : ℝ) - 1) := by sorry

end NeedPersuasion.FullInfo
