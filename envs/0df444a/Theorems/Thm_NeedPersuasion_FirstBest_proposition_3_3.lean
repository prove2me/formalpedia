-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_proposition_3_3
-- name    : NeedPersuasion.FirstBest.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:54.550185+00:00
-- url     : https://prove2.me/theorems/0b54aa80-80db-4200-8af0-63e66c47d0ca
-- title:
--   Proposition 3(3), p. 18 — ni is Pareto-dominated by a signaling mechanism iff λ_H ∈ [0, Λ̄_H); no L-user joins under ni iff λ_H ≥ Λ̄_H
-- statement:
--   Let $\bar\Lambda_H\in(0,1)$ be the root of $g(x)=\sum_{k\in\mathbb N_0}(1-x)x^ku_L(k)$, and let $p$ be an equilibrium joining probability of the no-information mechanism ni. Then
--
--   $$\text{some }\hat\pi\in\Pi_{SM}\text{ Pareto-dominates }\pi(p)\iff\lambda_H\in[0,\bar\Lambda_H),$$
--
--   and no low-need user joins under ni ($p=0$) if and only if $\lambda_H\ge\bar\Lambda_H$. Thus $\bar\Lambda_H$ is the smallest high-need arrival rate under which no low-need user joins in the equilibrium of ni.
--
--   **Formalization Note** $\bar\Lambda_H$ enters as any $\Lambda\in(0,1)$ with $g(\Lambda)=0$; the root is unique by the companion statement on $g$. $\lambda_H\ge0$ is a standing assumption.
-- source:
--   arXiv:2005.07253v3, Proposition 3(3), p. 18

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem proposition_3_3 (M : Model) (hM : M.Standing)
    (Λ : ℝ) (hΛ : Λ ∈ Set.Ioo (0 : ℝ) 1 ∧ g M Λ = 0) (p : ℝ) (hp : IsNIEquilibrium M p) :
    ((∃ π ∈ PiSM M, Dominates M π (niDist M p)) ↔ M.lamH < Λ) ∧ (p = 0 ↔ Λ ≤ M.lamH) := by sorry

end NeedPersuasion.FirstBest
