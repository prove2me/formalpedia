-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_lemma_5_1
-- name    : NeedPersuasion.FullInfo.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:08.731105+00:00
-- url     : https://prove2.me/theorems/e3e47793-64d7-40ac-ab93-09fd8804c994
-- title:
--   Lemma 5(1), p. 37 — W_H(x) is strictly decreasing in the threshold x ∈ ℝ_+ (for λ_H > 0)
-- statement:
--   Assume the standing assumptions, $\lambda_H>0$, and that $\sum_n\lambda_H^nu_H(n)$ converges. Then the H-type welfare of the threshold policies,
--   $$x\mapsto W_H(x)=W_H(\pi_x),$$
--   is strictly decreasing on $[0,\infty)$.
--
--   Admitting more L users congests the queue for the H users; this monotonicity is what makes a lower threshold always better for type H.
--
--   **Formalization Note** The hypothesis $\lambda_H>0$ is added: for $\lambda_H=0$ the function $W_H$ is identically $0$, and the paper's statement is meant for $\lambda_H>0$. The summability hypothesis makes every threshold policy an admission policy with finite H welfare (without it Lean's sums would default to $0$).
-- source:
--   arXiv:2005.07253v3, Lemma 5(1), p. 37

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem lemma_5_1 (M : Model) (hM : M.Standing) (hH : 0 < M.lamH)
    (hFin : Summable (fun n : ℕ => M.lamH ^ n * M.uH n)) :
    StrictAntiOn (WHx M) (Set.Ici 0) := by sorry

end NeedPersuasion.FullInfo
