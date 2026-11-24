-- Prove2me | Theorems.Thm_GomoryGroup_Rel_Supplement_theorem_4
-- name    : GomoryGroup.Rel.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:21:31.625835+00:00
-- url     : https://prove2.me/theorems/78e160ee-3d9d-4c34-baa7-9df05a6ec529
-- title:
--   THEOREM 4, p. 264 (bound corrected to > D) — if Π(y_i + 1) > D, the optimal solution of (4) is not unique
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $N$ an integer $m\times n$ matrix, $c_B\in\mathbb R^m$, $c_N\in\mathbb R^n$, $b\in\mathbb Z^m$, $D=|\det B|$, and let $y\in\mathbb N^n$ be an optimal solution of the group problem (4). If
--   $$\prod_{i=1}^n(y_i+1)>D,$$
--   then (4) has another optimal solution $y'\neq y$.
--
--   This bears on the multiplicity of optimal solutions of integer programs: a long optimal solution of the group problem is never unique.
--
--   **Formalization Note** The paper prints the hypothesis as $\prod(y_i+1)>D-1$, which is false: for $m=n=1$, $B=(2)$, $N=(1)$, $c_B=2$, $c_N=0$, $b=1$, the group problem is $\max -y$ over odd $y$, whose unique optimum $y=1$ has $\prod(y_i+1)=2>D-1=1$. The statement here uses $>D$, the bound under which the counting argument (more sub-vectors $0\le y'\le y$ than group elements) applies. Only $\det B\neq0$ is assumed; the other standing assumptions are not needed.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 264, THEOREM 4 (hypothesis corrected from > D − 1 to > D)

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel.Supplement

open Matrix

theorem theorem_4 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0)
    (y : Fin n → ℕ) (hy : IsGroupOptimal B N cB cN b y)
    (hprod : detD B < ∏ j, (y j + 1)) :
    ∃ y' : Fin n → ℕ, y' ≠ y ∧ IsGroupOptimal B N cB cN b y' := by sorry

end GomoryGroup.Rel.Supplement
