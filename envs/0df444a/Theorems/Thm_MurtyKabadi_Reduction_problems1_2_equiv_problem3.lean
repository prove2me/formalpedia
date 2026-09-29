-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problems1_2_equiv_problem3
-- name    : MurtyKabadi.Reduction.problems1_2_equiv_problem3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:18:07.420783+00:00
-- url     : https://prove2.me/theorems/8a64ac0d-9d67-4cbc-86cd-8db40e02d293
-- title:
--   Proof of Theorem 2, p. 125 — Problems 1 and 2 are equivalent to Problem 3
-- statement:
--   Let $D$ be a real square matrix indexed by a finite set and $Q(x) = x^{\mathsf T}Dx$. Then
--
--   1. $x = 0$ is not a local minimum of $Q$ on $\{x \ge 0\}$ if and only if there is an $x \ge 0$ with $Q(x) < 0$;
--   2. $Q$ is not bounded below on $\{x \ge 0\}$ if and only if there is an $x \ge 0$ with $Q(x) < 0$.
--
--   In other words, for the QP (7), local optimality of the origin, boundedness of the objective, and copositivity of $D$ are the same property. This is what makes testing local minimality of a feasible point as hard as testing copositivity.
--
--   **Formalization Note** Local minimality is relative to the orthant (`IsLocalMinOn` on $\{x \ge 0\}$). No symmetry or integrality of $D$ is needed.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 125, proof of Theorem 2, second paragraph; p. 122, remark after Problem 2

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

namespace MurtyKabadi.Reduction

theorem problems1_2_equiv_problem3 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) :
    (Problem1 D ↔ Problem3 D) ∧ (Problem2 D ↔ Problem3 D) := by sorry

end MurtyKabadi.Reduction
