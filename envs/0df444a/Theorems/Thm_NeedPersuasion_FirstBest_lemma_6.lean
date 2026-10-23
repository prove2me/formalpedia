-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_lemma_6
-- name    : NeedPersuasion.FirstBest.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:58.313084+00:00
-- url     : https://prove2.me/theorems/8b12c833-bbd3-4013-b27d-dae54e905384
-- title:
--   Lemma 6, p. 39 — L(x) is strictly decreasing while non-negative and stays negative afterwards; L(x) ≤ max{inf_{0≤u≤x} L(u), 0}
-- statement:
--   For a threshold $x\in\mathbb R_+$ let $L(x)$ be the (LEAVE) value of the threshold policy $\pi_x$. Then:
--
--   1. $L$ is strictly decreasing as long as it is non-negative: for $0\le x<y$ with $L(y)\ge0$, $L(y)<L(x)$;
--   2. once negative, it stays negative: for $0\le x\le y$ with $L(x)<0$, $L(y)<0$;
--   3. formally, for every $x\ge0$,
--   $$L(x)\le\max\Big\{\inf_{0\le u\le x}L(u),\,0\Big\}.$$
--
--   Together these give at most one threshold $\bar x$ with $L(\bar x)=0$.
--
--   **Formalization Note** The prose of the lemma (items 1–2) is stated alongside its "formally" clause (item 3), which alone is weaker. The proof's last line writes $L(y)$ inside the infimum; the statement's $L(u)$ is used.
-- source:
--   arXiv:2005.07253v3, Lemma 6, p. 39

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem lemma_6 (M : Model) (hM : M.Standing) :
    (∀ x y : ℝ, 0 ≤ x → x < y → 0 ≤ leaveValx M y → leaveValx M y < leaveValx M x) ∧
    (∀ x y : ℝ, 0 ≤ x → x ≤ y → leaveValx M x < 0 → leaveValx M y < 0) ∧
    (∀ x : ℝ, 0 ≤ x →
      leaveValx M x ≤ max (sInf (leaveValx M '' Set.Icc 0 x)) 0) := by sorry

end NeedPersuasion.FirstBest
