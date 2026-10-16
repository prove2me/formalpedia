-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_lemma_5_2
-- name    : NeedPersuasion.FullInfo.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:09.085995+00:00
-- url     : https://prove2.me/theorems/984a0973-61c3-449b-a7ca-10a3acbbb538
-- title:
--   Lemma 5(2), p. 37 — W_L(x) is monotone between consecutive integers and unimodal on ℝ_+
-- statement:
--   Assume the standing assumptions, and let $W_L(x)=W_L(\pi_x)$ be the L-type welfare of the threshold policy with threshold $x\ge0$. Then
--   1. for every $m\in\mathbb N_0$, $W_L$ is monotone (non-decreasing or non-increasing) on $[m,m+1]$;
--   2. $W_L$ is unimodal: there is $x^\star\ge0$ such that $W_L$ is non-decreasing on $[0,x^\star]$ and non-increasing on $[x^\star,\infty)$.
--
--   Unimodality is how the paper compares the full-information threshold $m_{fi}$ with every smaller threshold using only the two values $W_L(m_{fi}-1)$ and $W_L(m_{fi})$.
-- source:
--   arXiv:2005.07253v3, Lemma 5(2), p. 37

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem lemma_5_2 (M : Model) (hM : M.Standing) :
    (∀ m : ℕ, MonotoneOn (WLx M) (Set.Icc (m : ℝ) (m + 1)) ∨
      AntitoneOn (WLx M) (Set.Icc (m : ℝ) (m + 1))) ∧
    ∃ xstar : ℝ, 0 ≤ xstar ∧ MonotoneOn (WLx M) (Set.Icc 0 xstar) ∧
      AntitoneOn (WLx M) (Set.Ici xstar) := by sorry

end NeedPersuasion.FullInfo
