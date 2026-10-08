-- Prove2me | Theorems.Thm_FuzzyGames_Values_monomial_value
-- name    : FuzzyGames.Values.monomial_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:43.668792+00:00
-- url     : https://prove2.me/theorems/04e7e6b3-2427-4490-8ba8-e1de376a6ad4
-- title:
--   Theorem 8.1, proof — the axioms force (ψ_n τ^k)_i = k_i/(k_1+⋯+k_n), as formula (4) gives
-- statement:
--   Let $(\psi_n)$ be any family of maps $\psi_n:V^n\to\mathbb R^n$ satisfying the Pareto optimality, symmetry and atomicity axioms (no linearity or continuity is assumed). Let $k\in\mathbb N^n$ with $k\neq0$, and let $v\in V^n$ be the monomial $v(\tau)=\tau_1^{k_1}\cdots\tau_n^{k_n}$. Then for every player $i$
--   $$(\psi_n v)_i=\frac{k_i}{k_1+k_2+\cdots+k_n},$$
--   and the diagonal formula (4) gives the same value: $\int_0^1\partial_i v(t\tau^N)\,dt=k_i/(k_1+\cdots+k_n)$.
--
--   With the density of the monomials in $V^n$, this proves that a sequence of fuzzy values is unique.
--
--   **Formalization Note** Exponents with some $k_i=0$ are included; the corresponding player then receives $0$. The atomicity axiom used is the one with nonempty types (surjective partition maps). $k\ne0$ forces $n\ge1$ and a positive denominator.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8, proof of Theorem 8.1, p. 11

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

namespace FuzzyGames.Values

/-- §8, proof of Theorem 8.1 (p. 11): with Pareto optimality, symmetry and atomicity,
`(ψ_n v)_i = k_i / (k_1 + ⋯ + k_n)` when `v(τ) = τ_1^{k_1} ⋯ τ_n^{k_n}` (`k ≠ 0`), which
agrees with formula (4). -/
theorem monomial_value (ψ : (n : ℕ) → Vn n → (Fin n → ℝ))
    (hP : IsParetoOptimal ψ) (hS : IsSymmetric ψ) (hA : IsAtomic ψ) (n : ℕ)
    (k : Fin n → ℕ) (hk : k ≠ 0) (v : Vn n) (hv : ∀ τ : Fin n → ℝ, v.1 τ = monomial k τ)
    (i : Fin n) :
    ψ n v i = (k i : ℝ) / ((∑ j, k j : ℕ) : ℝ) ∧
      diagValue v.1 i = (k i : ℝ) / ((∑ j, k j : ℕ) : ℝ) := by sorry

end FuzzyGames.Values
