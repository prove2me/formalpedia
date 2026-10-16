-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_theorem_5
-- name    : NeedPersuasion.FirstBest.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:52.468108+00:00
-- url     : https://prove2.me/theorems/6c71c8d6-cf56-4d4b-8e67-ab0904bdf296
-- title:
--   Theorem 5, p. 19 — exactly one of: ni is Pareto-efficient among admission policies, or a signaling mechanism Pareto-dominates ni; the first iff p_ni = 0
-- statement:
--   Let $p$ be an equilibrium joining probability of the no-information mechanism ni, with steady state $\pi(p)$. Exactly one of the following holds:
--
--   1. $\pi(p)$ is Pareto-efficient within the class $\Pi_{AP}$ of admission policies;
--   2. some signaling mechanism $\hat\pi\in\Pi_{SM}$ Pareto-dominates $\pi(p)$.
--
--   Moreover, the first case occurs if and only if $p=0$, i.e. all low-need users choose their outside option under ni.
--
--   **Formalization Note** "Exactly one" is an exclusive or. The statement holds for every equilibrium $p$ of ni.
-- source:
--   arXiv:2005.07253v3, Theorem 5, p. 19

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem theorem_5 (M : Model) (hM : M.Standing) (p : ℝ) (hp : IsNIEquilibrium M p) :
    Xor (ParetoEfficientIn M (PiAP M) (niDist M p))
        (∃ π ∈ PiSM M, Dominates M π (niDist M p)) ∧
      (ParetoEfficientIn M (PiAP M) (niDist M p) ↔ p = 0) := by sorry

end NeedPersuasion.FirstBest
