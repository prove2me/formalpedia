-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problems11_12_equiv
-- name    : MurtyKabadi.Reduction.problems11_12_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:18:41.006453+00:00
-- url     : https://prove2.me/theorems/51339b44-6d34-4432-b89f-a4dfcb214e80
-- title:
--   §4, p. 127 — Problems 11 and 12 are equivalent to Problems 1 and 2
-- statement:
--   Let $D$ be a real square matrix of order $n$ and
--   $$h(u) = (u_1^2, \dots, u_n^2)\, D\, (u_1^2, \dots, u_n^2)^{\mathsf T}, \qquad u \in \mathbb R^n,$$
--   the objective of the unconstrained problem (15). Then
--
--   1. $u = 0$ is not a local minimum of $h$ on $\mathbb R^n$ if and only if $x = 0$ is not a local minimum of $Q(x) = x^{\mathsf T}Dx$ on $\{x \ge 0\}$ (Problem 11 $\iff$ Problem 1);
--   2. $h$ is not bounded below on $\mathbb R^n$ if and only if $Q$ is not bounded below on $\{x \ge 0\}$ (Problem 12 $\iff$ Problem 2).
--
--   This carries the hardness of the constrained problems over to smooth unconstrained minimization of a polynomial of degree four.
--
--   **Formalization Note** No symmetry or integrality of $D$ is needed.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 127, §4 (Problems 1 and 11, and 2 and 12, are equivalent)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

namespace MurtyKabadi.Reduction

theorem problems11_12_equiv {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) :
    (Problem11 D ↔ Problem1 D) ∧ (Problem12 D ↔ Problem2 D) := by sorry

end MurtyKabadi.Reduction
