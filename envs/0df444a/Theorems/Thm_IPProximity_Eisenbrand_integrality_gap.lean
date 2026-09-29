-- Prove2me | Theorems.Thm_IPProximity_Eisenbrand_integrality_gap
-- name    : IPProximity.Eisenbrand.integrality_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:33:52.465729+00:00
-- url     : https://prove2.me/theorems/fa48c45e-16cc-442e-bbb0-e372fd2abee9
-- title:
--   Eq. (21) — integrality gap ≤ ‖c‖∞ · m(2mΔ+1)^m
-- statement:
--   Let $m,n\ge 0$, let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ and $u\in\mathbb N^n$. The integer program (10) of Eisenbrand and Weismantel is
--   $$\max\{c^{T}x : Ax=b,\ 0\le x\le u,\ x\in\mathbb Z^n\},$$
--   and its linear programming (LP) relaxation is the same problem with $x\in\mathbb R^n$. Let $\Delta\in\mathbb N$ with $|a_{ij}|\le\Delta$, let $x^*$ be an optimal vertex solution of the LP relaxation, and let $z^*$ be any optimal solution of the integer program (10). Then the (absolute) integrality gap satisfies
--   $$c^{T}(x^*-z^*)\ \le\ \|c\|_\infty\cdot m\cdot(2\,m\,\Delta+1)^m ,\qquad \|c\|_\infty=\max_i|c_i| .$$
--
--   **Formalization Note** The paper derives (21) for the $z^*$ of Theorem 3.3; since all optimal integer solutions have the same objective value, the statement is given for every optimal integer solution. $\|c\|_\infty$ is Mathlib's sup norm of the real vector $(c_i)_i$ (equal to $0$ when $n=0$).
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:9, Sect. 3.1, Eq. (21)

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal

namespace IPProximity.Eisenbrand

/-- Eq. (21) (p. 5:9): the absolute integrality gap of (10) at an optimal LP vertex `x` is at
most `‖c‖∞·m·(2mΔ + 1)ᵐ`, for every optimal integer solution `z`. The norm of the real vector
`(cᵢ)ᵢ` below is Mathlib's sup norm on `Fin n → ℝ`, i.e. `‖c‖∞`. -/
theorem integrality_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (hvert : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (z : Fin n → ℤ) (hz : IsIPOptimal A b c u z) :
    dotProduct (fun i => (c i : ℝ)) x - dotProduct (fun i => (c i : ℝ)) (fun i => (z i : ℝ)) ≤
      ‖(fun i => (c i : ℝ))‖ * ((m : ℝ) * (2 * m * Δ + 1) ^ m) := by sorry

end IPProximity.Eisenbrand
