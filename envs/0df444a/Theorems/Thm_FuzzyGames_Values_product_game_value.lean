-- Prove2me | Theorems.Thm_FuzzyGames_Values_product_game_value
-- name    : FuzzyGames.Values.product_game_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:27.431664+00:00
-- url     : https://prove2.me/theorems/94cdd3ab-2dea-4908-8401-206b1b7e77fa
-- title:
--   Theorem 8.1, proof — Pareto optimality and symmetry give ψ_n(τ_1⋯τ_n) = (v(τ^N)/n) τ^N
-- statement:
--   Let $(\psi_n)$ be any family of maps $\psi_n:V^n\to\mathbb R^n$ satisfying the Pareto optimality and symmetry axioms (no linearity, continuity or atomicity is assumed). Let $n\ge1$ and let $v\in V^n$ be the product game $v(\tau)=\tau_1\tau_2\cdots\tau_n$. Then
--   $$\psi_n v=\frac{v(\tau^N)}{n}\,\tau^N ,$$
--   that is, every player receives $1/n$.
--
--   This is the base case of the computation of $\psi_n$ on monomials in the uniqueness proof of Theorem 8.1.
--
--   **Formalization Note** The axioms are the predicates of the definitions module, applied to an arbitrary family of functions. The product game is in $V^n$ only for $n\ge1$, hence the hypothesis $n\ge1$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8, proof of Theorem 8.1, pp. 10–11

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

namespace FuzzyGames.Values

/-- §8, proof of Theorem 8.1 (p. 11): Pareto optimality and symmetry imply
`ψ_n v = (v(τ^N)/n) τ^N` when `v(τ) = τ_1 τ_2 ⋯ τ_n`. -/
theorem product_game_value (ψ : (n : ℕ) → Vn n → (Fin n → ℝ))
    (hP : IsParetoOptimal ψ) (hS : IsSymmetric ψ) (n : ℕ) (hn : 0 < n) (v : Vn n)
    (hv : ∀ τ : Fin n → ℝ, v.1 τ = ∏ i, τ i) :
    ψ n v = (v.1 1 / n) • (1 : Fin n → ℝ) := by sorry

end FuzzyGames.Values
