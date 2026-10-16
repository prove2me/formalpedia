-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_lemma_5_1
-- name    : NeedPersuasion.FirstBest.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:55.356996+00:00
-- url     : https://prove2.me/theorems/ac621d38-159b-4806-9b63-cbc5bec2a6fd
-- title:
--   Lemma 5(1), p. 37 — the high-need welfare W_H(x) of the threshold policy x is strictly decreasing in x ∈ R_+
-- statement:
--   Suppose $\lambda_H>0$. The high-need welfare of the threshold policy $x$,
--   $$W_H(x)=\lambda_H\sum_{n\ge0}\pi_{x,n}\,u_H(n),$$
--   is strictly decreasing in $x\in\mathbb R_+$.
--
--   Raising the threshold admits more low-need users and congests the queue for high-need users.
--
--   **Formalization Note** $\lambda_H>0$ is added: for $\lambda_H=0$, $W_H\equiv0$ and the claim fails. Convergence of $\sum_k\lambda_H^ku_H(k)$ is added: the tail of $\pi_x$ is geometric with ratio $\lambda_H$, so this is exactly the condition under which $W_H(x)$ is a convergent series (the paper treats it as finite); without it the Lean series has the junk value $0$ and $W_H$ would be constant.
-- source:
--   arXiv:2005.07253v3, Lemma 5(1), p. 37

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem lemma_5_1 (M : Model) (hM : M.Standing) (hH : 0 < M.lamH)
    (hSumH : Summable (fun k => M.lamH ^ k * M.uH k)) :
    StrictAntiOn (WHx M) (Set.Ici 0) := by sorry

end NeedPersuasion.FirstBest
