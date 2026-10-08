-- Prove2me | Theorems.Thm_L0BnB_Duality_weak_duality
-- name    : L0BnB.Duality.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:02.906324+00:00
-- url     : https://prove2.me/theorems/ac1c05db-1e7c-49de-a0c7-78044f4f47e8
-- title:
--   Theorem 2, (20)–(22) — weak duality: $h_1$ and $h_2$ bound the reduced relaxation (5) from below
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M>0$, and let $F$ be the objective of the reduced relaxation (5), minimized over $\|\beta\|_\infty\le M$.
--
--   1. If $\sqrt{\lambda_0/\lambda_2}\le M$, then for every $\alpha\in\mathbb R^n$, every $\gamma\in\mathbb R^p$ and every $\beta$ with $\|\beta\|_\infty\le M$,
--   $$ h_1(\alpha,\gamma)\le F(\beta). $$
--   2. If $\sqrt{\lambda_0/\lambda_2}>M$, then for every $(\rho,\mu)\in\mathbb R^n\times\mathbb R^p$ with $|\rho^TX_i|-\mu_i\le\lambda_0/M+\lambda_2M$ for all $i\in[p]$, and every $\beta$ with $\|\beta\|_\infty\le M$,
--   $$ h_2(\rho,\mu)\le F(\beta). $$
--
--   Here $h_1$ is the objective of (20)–(21) and $h_2$ that of (22). This is the "a dual of Problem (5) is given by" half of Theorem 2: every dual feasible point gives a valid lower bound on the relaxation, which is how the branch-and-bound algorithm prunes nodes from inexact primal solutions.
--
--   **Formalization Note** The dual (20) is unconstrained, so part 1 quantifies over all $(\alpha,\gamma)$; $\mu$ in (22) is not sign-constrained.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 13, Theorem 2, (20)–(22); p. 31, Proof of Theorem 2, (48)–(49)

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

namespace L0BnB.Duality

/-- Theorem 2, (20)–(22), p. 13 — weak duality. If `√(λ₀/λ₂) ≤ M`, then `h₁(α, γ) ≤ L0BnB.Reduced.F(β)` for
every `α ∈ ℝⁿ`, every `γ ∈ ℝᵖ` (the dual (20) is unconstrained) and every `β` feasible for (5).
If `√(λ₀/λ₂) > M`, then `h₂(ρ, μ) ≤ L0BnB.Reduced.F(β)` for every `(ρ, μ)` satisfying the constraint of (22)
and every `β` feasible for (5). -/
theorem weak_duality {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      ∀ (α : Fin n → ℝ) (γ : Fin p → ℝ), ∀ β ∈ L0BnB.Reduced.box p M,
        h1 X y lam0 lam2 M α γ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) ∧
    (M < Real.sqrt (lam0 / lam2) →
      ∀ (ρ : Fin n → ℝ) (μ : Fin p → ℝ), Feas22 X lam0 lam2 M ρ μ → ∀ β ∈ L0BnB.Reduced.box p M,
        h2 y M ρ μ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) := by sorry

end L0BnB.Duality
