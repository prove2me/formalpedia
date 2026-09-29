-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problems3_4_equiv
-- name    : MurtyKabadi.Reduction.problems3_4_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:17:46.751796+00:00
-- url     : https://prove2.me/theorems/fd6b2f16-7aaf-4b71-af10-3d9a4985ba9f
-- title:
--   Proof of Theorem 2, p. 125 — Problems 3 and 4 are equivalent
-- statement:
--   Let $D$ be a real square matrix indexed by a finite set, $Q(x) = x^{\mathsf T}Dx$, and let $a_0 > 0$. Then there is an $x \ge 0$ with $Q(x) < 0$ if and only if there is an $x \ge 0$ with $e^{\mathsf T}x = a_0$ and $Q(x) < 0$:
--   $$\text{Problem 3 for } D \iff \text{Problem 4 for } (D, a_0).$$
--
--   It transfers the hardness of Problem 4 to the plain question "is $D$ not copositive".
--
--   **Formalization Note** The paper's $a_0$ is a positive integer; the statement is made for every real $a_0 > 0$, which includes it.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 125, proof of Theorem 2, second paragraph

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

namespace MurtyKabadi.Reduction

theorem problems3_4_equiv {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (a0 : ℝ) (ha0 : 0 < a0) :
    Problem3 D ↔ Problem4 D a0 := by sorry

end MurtyKabadi.Reduction
