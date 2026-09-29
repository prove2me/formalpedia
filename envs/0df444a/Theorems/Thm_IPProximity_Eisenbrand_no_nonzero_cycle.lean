-- Prove2me | Theorems.Thm_IPProximity_Eisenbrand_no_nonzero_cycle
-- name    : IPProximity.Eisenbrand.no_nonzero_cycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:31:41.580035+00:00
-- url     : https://prove2.me/theorems/c16c7d91-a444-4f77-9fc0-86c6021ee688
-- title:
--   Lemma 3.2 — a closest integer optimum admits no nonzero cycle
-- statement:
--   Let $m,n\ge 0$, let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ and $u\in\mathbb N^n$. The integer program (10) of Eisenbrand and Weismantel is
--   $$\max\{c^{T}x : Ax=b,\ 0\le x\le u,\ x\in\mathbb Z^n\},$$
--   and its linear programming (LP) relaxation is the same problem with $x\in\mathbb R^n$. Let $x^*$ be an optimal solution of the LP relaxation and let $z^*$ be an optimal solution of the integer program such that $\|z^*-x^*\|_1=\sum_i|z^*_i-x^*_i|$ is minimal among all optimal integer solutions. Then there is no nonzero cycle of $z^*-x^*$:
--   $$\neg\,\exists\,y\in\mathbb Z^n\setminus\{0\}:\ Ay=0,\ |y_i|\le|(z^*-x^*)_i|,\ y_i(z^*-x^*)_i\ge0\ \ \forall i.$$
--
--   The paper states "There does not exist a cycle of $z^*-x^*$"; since the zero vector satisfies Eq. (14), the statement is read, as the paper's proof requires, for nonzero cycles.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:8, Lemma 3.2

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsCycle

namespace IPProximity.Eisenbrand

/-- Lemma 3.2 (p. 5:8), with the implicit `y ≠ 0`: if `x` is LP-optimal and `z` is an optimal
integer solution of (10) minimizing `‖z - x‖₁` among optimal integer solutions, then `z - x` has
no nonzero cycle. -/
theorem no_nonzero_cycle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (x : Fin n → ℝ) (z : Fin n → ℤ)
    (hx : IsLPOptimal A b c u x) (hz : IsIPOptimal A b c u z)
    (hmin : ∀ z' : Fin n → ℤ, IsIPOptimal A b c u z' →
      ∑ i, |(z i : ℝ) - x i| ≤ ∑ i, |(z' i : ℝ) - x i|) :
    ¬ ∃ y : Fin n → ℤ, y ≠ 0 ∧ IsCycle A z x y := by sorry

end IPProximity.Eisenbrand
