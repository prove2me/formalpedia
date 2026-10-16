-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_leave_fi_neg
-- name    : NeedPersuasion.FullInfo.leave_fi_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:17.840854+00:00
-- url     : https://prove2.me/theorems/0e0e3496-4a17-4f84-95d4-47c7c4f01775
-- title:
--   App. C, proof of Theorem 4, p. 43 — fi is a signaling mechanism and (LEAVE) does not bind at fi: L(m_fi) < 0
-- statement:
--   Assume the standing assumptions and that $\sum_n\lambda_H^nu_H(n)$ converges. Then the full-information mechanism is a signaling mechanism, and its (LEAVE) constraint is slack:
--   $$\mathsf{fi}\in\Pi_{SM}\qquad\text{and}\qquad L(\mathsf{fi})<0 .$$
--
--   Under full information an L user told to leave knows the queue has at least $m_{fi}$ users, where joining has negative utility; this is the step that lets Theorem 3 apply to $\mathsf{fi}$.
--
--   **Formalization Note** The summability hypothesis guarantees that $\mathsf{fi}$ has finite H welfare and so belongs to $\Pi_{AP}$ as defined in this mission.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Theorem 4, p. 43

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem leave_fi_neg (M : Model) (hM : M.Standing)
    (hFin : Summable (fun n : ℕ => M.lamH ^ n * M.uH n)) :
    fi M ∈ PiSM M ∧ leaveVal M (fi M) < 0 := by sorry

end NeedPersuasion.FullInfo
