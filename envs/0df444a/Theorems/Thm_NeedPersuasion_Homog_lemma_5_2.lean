-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_lemma_5_2
-- name    : NeedPersuasion.Homog.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:59.8546+00:00
-- url     : https://prove2.me/theorems/d37fa540-cf04-4ffc-a0a2-4624b14e85ce
-- title:
--   Lemma 5(2), p. 37 — the threshold welfare W_L(x) is unimodal and monotone between consecutive integers
-- statement:
--   Consider the congested-service model under its standing assumptions. For a threshold $x \ge 0$ let $W_L(x)$ be the welfare of low-need users under the threshold policy $\pi_x$ (L-users join below $\lfloor x\rfloor$, join with probability $x - \lfloor x\rfloor$ at $\lfloor x\rfloor$, and leave above). Then:
--
--   1. on every interval $[m, m+1]$ with $m \in \mathbb N_0$, the function $x \mapsto W_L(x)$ is monotone (non-decreasing or non-increasing);
--   2. $W_L$ is unimodal on $\mathbb R_+$: there is $x^\star \ge 0$ such that
--   $$W_L \text{ is non-decreasing on } [0, x^\star] \quad\text{and non-increasing on } [x^\star, \infty).$$
--
--   Unimodality lets one compare a threshold policy with the policies at the neighbouring integers, which is how the proof of Proposition 1 bounds the optimal signaling mechanism.
--
--   **Formalization Note** The lemma is stated for general $\lambda_H \ge 0$, as in the paper; this mission's homogeneous hypothesis $\lambda_H = 0$ is not assumed.
-- source:
--   arXiv:2005.07253v3, Lemma 5(2), p. 37; proof pp. 38–39

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model

namespace NeedPersuasion.Homog

theorem lemma_5_2 (M : Model) (hM : M.Standing) :
    (∀ m : ℕ, MonotoneOn (WLx M) (Set.Icc (m : ℝ) (m + 1)) ∨
        AntitoneOn (WLx M) (Set.Icc (m : ℝ) (m + 1))) ∧
      ∃ xstar : ℝ, 0 ≤ xstar ∧ MonotoneOn (WLx M) (Set.Icc 0 xstar) ∧
        AntitoneOn (WLx M) (Set.Ici xstar) := by sorry

end NeedPersuasion.Homog
