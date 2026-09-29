-- Prove2me | Theorems.Thm_IPProximity_Eisenbrand_cycle_exchange
-- name    : IPProximity.Eisenbrand.cycle_exchange
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:30:55.020561+00:00
-- url     : https://prove2.me/theorems/676e56f9-f8ad-4129-94c5-3bab75623ff1
-- title:
--   Lemma 3.1 — exchanging a cycle keeps both solutions feasible
-- statement:
--   Let $m,n\ge 0$, let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ and $u\in\mathbb N^n$. The integer program (10) of Eisenbrand and Weismantel is
--   $$\max\{c^{T}x : Ax=b,\ 0\le x\le u,\ x\in\mathbb Z^n\},$$
--   and its linear programming (LP) relaxation is the same problem with $x\in\mathbb R^n$. Let $x^*$ be an optimal solution of the LP relaxation and $z^*$ an optimal solution of the integer program. If $y\in\mathbb Z^n$ is a cycle of $z^*-x^*$ (Eq. (14)), then:
--
--   1. $z^*-y$ is a feasible integer solution of (10);
--   2. $x^*+y$ is a feasible solution of the LP relaxation of (10);
--   3. $$c^{T}y\le 0.$$
--
--   This lemma is the exchange step behind the proximity bound: a cycle can be moved from the integer optimum towards the LP optimum without losing feasibility or objective value on the integer side.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:8, Lemma 3.1

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsCycle

namespace IPProximity.Eisenbrand

/-- Lemma 3.1 (p. 5:8): if `x` is LP-optimal, `z` is IP-optimal for (10) and `y` is a cycle of
`z - x`, then (i) `z - y` is integer feasible, (ii) `x + y` is LP feasible, (iii) `cᵀy ≤ 0`. -/
theorem cycle_exchange {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (x : Fin n → ℝ) (z : Fin n → ℤ)
    (hx : IsLPOptimal A b c u x) (hz : IsIPOptimal A b c u z)
    (y : Fin n → ℤ) (hy : IsCycle A z x y) :
    z - y ∈ ipFeasible A b u ∧
      (x + fun i => (y i : ℝ)) ∈ lpPolytope A b u ∧
      dotProduct c y ≤ 0 := by sorry

end IPProximity.Eisenbrand
