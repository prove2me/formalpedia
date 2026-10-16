-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_g_unique_root
-- name    : NeedPersuasion.FirstBest.g_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:50.098016+00:00
-- url     : https://prove2.me/theorems/af38f701-a9bb-42eb-bc2f-d16122747db1
-- title:
--   App. C, proof of Proposition 3, p. 42 — g(x) = Σ(1−x)x^k u_L(k) is strictly decreasing on [0,1) with a unique root Λ̄_H ∈ (0,1)
-- statement:
--   Let
--   $$g(x)=\sum_{k\in\mathbb N_0}(1-x)\,x^k\,u_L(k),\qquad x\in[0,1),$$
--   the expected utility of a low-need user joining an M/M/1 queue with load $x$. Then $g$ is strictly decreasing on $[0,1)$, and there is a unique $\bar\Lambda_H\in(0,1)$ with $g(\bar\Lambda_H)=0$.
--
--   This root is the threshold $\bar\Lambda_H$ of Proposition 3(3) and Theorem 6.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 3, p. 42

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem g_unique_root (M : Model) (hM : M.Standing) :
    StrictAntiOn (g M) (Set.Ico 0 1) ∧ ∃! Λ : ℝ, Λ ∈ Set.Ioo (0 : ℝ) 1 ∧ g M Λ = 0 := by sorry

end NeedPersuasion.FirstBest
