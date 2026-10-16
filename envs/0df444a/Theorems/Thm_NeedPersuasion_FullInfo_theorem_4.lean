-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_theorem_4
-- name    : NeedPersuasion.FullInfo.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:26.603401+00:00
-- url     : https://prove2.me/theorems/2778a480-6564-4302-9bbe-8f158f55f8ca
-- title:
--   Theorem 4, pp. 18–19 — exactly one of: fi is Pareto-efficient among admission policies; some signaling mechanism Pareto-dominates fi; the first iff W_L(m_fi) > W_L(m_fi − 1)
-- statement:
--   Assume the standing assumptions, $\lambda_H>0$, that $\sum_n\lambda_H^nu_H(n)$ converges, and that $\lambda<1$ or $u_L(k),u_H(k)\to-\infty$. Then exactly one of the following two statements holds:
--   1. the full-information mechanism $\mathsf{fi}$ is Pareto-efficient within $\Pi_{AP}$;
--   2. some signaling mechanism $\pi\in\Pi_{SM}$ Pareto-dominates $\mathsf{fi}$.
--
--   Moreover, the first case occurs if and only if
--   $$W_L(m_{fi})>W_L(m_{fi}-1).$$
--
--   The dichotomy says that revealing everything is either first-best efficient or strictly improvable by information design for both types at once, and the welfare comparison between the two adjacent thresholds decides which.
--
--   **Formalization Note** "Exactly one" is exclusive or. The condition $\lambda_H>0$ comes from §4.2's heterogeneous setting; without it the strict comparison fails at a tie. The hypothesis "$\lambda<1$ or $u_L,u_H\to-\infty$" is that of Lemma 2, whose existence result the converse direction of the proof uses; the summability hypothesis is the finite-welfare convention (it is equivalent to $\Pi_{AP}\ne\emptyset$ when $\lambda_H>0$). $W_L(m_{fi}-1)$ and $W_L(m_{fi})$ are the L welfare of the threshold policies $\pi_{m_{fi}-1}$ and $\pi_{m_{fi}}=\mathsf{fi}$.
-- source:
--   arXiv:2005.07253v3, Theorem 4, pp. 18–19

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem theorem_4 (M : Model) (hM : M.Standing) (hH : 0 < M.lamH)
    (hFin : Summable (fun n : ℕ => M.lamH ^ n * M.uH n))
    (hExist : M.lam < 1 ∨
      (Filter.Tendsto M.uL Filter.atTop Filter.atBot ∧
        Filter.Tendsto M.uH Filter.atTop Filter.atBot)) :
    Xor (ParetoEfficientIn M (PiAP M) (fi M)) (∃ π ∈ PiSM M, Dominates M π (fi M)) ∧
      (ParetoEfficientIn M (PiAP M) (fi M) ↔ WLx M ((mfi M : ℝ) - 1) < WLx M (mfi M)) := by sorry

end NeedPersuasion.FullInfo
