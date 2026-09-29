-- Prove2me | Theorems.Thm_IPProximity_Eisenbrand_l1_proximity
-- name    : IPProximity.Eisenbrand.l1_proximity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:33:29.595859+00:00
-- url     : https://prove2.me/theorems/ad5b4cec-8148-4323-a049-e041f780d483
-- title:
--   Theorem 3.3 — ℓ1-proximity: ‖z* − x*‖₁ ≤ m(2mΔ+1)^m
-- statement:
--   Let $m,n\ge 0$, let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ and $u\in\mathbb N^n$. The integer program (10) of Eisenbrand and Weismantel is
--   $$\max\{c^{T}x : Ax=b,\ 0\le x\le u,\ x\in\mathbb Z^n\},$$
--   and its linear programming (LP) relaxation is the same problem with $x\in\mathbb R^n$. Let $\Delta\in\mathbb N$ with $|a_{ij}|\le\Delta$ for all $i,j$, and assume that (10) has at least one feasible integer solution. Let $x^*$ be an optimal vertex solution of the LP relaxation, i.e. an optimal solution that is an extreme point of $\{x\in\mathbb R^n: Ax=b,\ 0\le x\le u\}$. Then there exists an optimal solution $z^*$ of the integer program (10) such that
--   $$\|z^*-x^*\|_1=\sum_{i=1}^n|z^*_i-x^*_i|\ \le\ m\cdot(2\,m\,\Delta+1)^m .$$
--
--   The bound depends only on the number of rows $m$ and the entry bound $\Delta$, not on the number of variables $n$ or on $b$, $c$, $u$; it is the main structural result of the paper and underlies its algorithms for integer programs with upper bounds.
--
--   **Formalization Note** The paper assumes implicitly that (10) has an optimal solution; this is added as the hypothesis that its integer feasible set is nonempty (the feasible set is finite, so an optimum then exists). $\Delta$ is a natural number.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:8, Theorem 3.3

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal

namespace IPProximity.Eisenbrand

/-- Theorem 3.3 (p. 5:8): for the integer program (10) with `|aᵢⱼ| ≤ Δ`, every optimal vertex
`x` of its LP relaxation has an optimal integer solution `z` with
`‖z - x‖₁ ≤ m·(2mΔ + 1)ᵐ`, provided (10) has an integer feasible point. -/
theorem l1_proximity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (hvert : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (hfeas : (ipFeasible A b u).Nonempty) :
    ∃ z : Fin n → ℤ, IsIPOptimal A b c u z ∧
      ∑ i, |(z i : ℝ) - x i| ≤ (m : ℝ) * (2 * m * Δ + 1) ^ m := by sorry

end IPProximity.Eisenbrand
