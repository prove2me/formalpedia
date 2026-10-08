-- Prove2me | Theorems.Thm_L0BnB_Duality_theorem_2
-- name    : L0BnB.Duality.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:40.957403+00:00
-- url     : https://prove2.me/theorems/9a9eb671-225f-4454-813b-d6d7d923fd62
-- title:
--   Theorem 2 — Lagrangian duals of the reduced relaxation (5) and their optimal dual variables
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ with columns $X_i$, $y\in\mathbb R^n$ and $\lambda_0,\lambda_2,M>0$. Let $\beta^*$ be an optimal solution of the reduced relaxation
--
--   $$
--   \min_{\beta\in\mathbb R^p}\ F(\beta)=\tfrac12\|y-X\beta\|_2^2+\sum_{i\in[p]}\psi(\beta_i;\lambda_0,\lambda_2,M)\quad\text{s.t.}\quad\|\beta\|_\infty\le M,\tag{5}
--   $$
--
--   and let $r^*=y-X\beta^*$.
--
--   1. If $\sqrt{\lambda_0/\lambda_2}\le M$, the problem
--   $$\max_{\alpha\in\mathbb R^n,\gamma\in\mathbb R^p} h_1(\alpha,\gamma)=-\tfrac12\|\alpha\|_2^2-\alpha^Ty-\sum_{i\in[p]}\Big(\Big[\frac{(\alpha^TX_i-\gamma_i)^2}{4\lambda_2}-\lambda_0\Big]_+ + M|\gamma_i|\Big)\tag{20}$$
--   is a dual of (5): $h_1(\alpha,\gamma)\le F(\beta)$ for all $\alpha,\gamma$ and all feasible $\beta$. Its optimal dual variables are $\alpha^*=-r^*$ and $\gamma^*_i=\mathbb 1_{[|\beta^*_i|=M]}(\alpha^{*T}X_i-2M\lambda_2\,\mathrm{sign}(\alpha^{*T}X_i))$, which satisfy $h_1(\alpha^*,\gamma^*)=F(\beta^*)$.
--   2. If $\sqrt{\lambda_0/\lambda_2}>M$, the problem
--   $$\max_{\rho\in\mathbb R^n,\mu\in\mathbb R^p} h_2(\rho,\mu)=-\tfrac12\|\rho\|_2^2-\rho^Ty-M\|\mu\|_1\quad\text{s.t.}\quad |\rho^TX_i|-\mu_i\le\lambda_0/M+\lambda_2M,\ i\in[p]\tag{22}$$
--   is a dual of (5): $h_2(\rho,\mu)\le F(\beta)$ for all feasible $(\rho,\mu)$ and all feasible $\beta$. Its optimal dual variables are $\rho^*=-r^*$ and $\mu^*_i=\mathbb 1_{[|\beta^*_i|=M]}(|\rho^{*T}X_i|-\lambda_0/M-\lambda_2M)$, which are feasible for (22) and satisfy $h_2(\rho^*,\mu^*)=F(\beta^*)$.
--
--   The closed-form dual variables are what make cheap dual bounds possible in the paper's branch-and-bound method: at an inexact primal solution $\hat\beta$, the choice $\hat\alpha=-\hat r$ imitates (23) and yields a valid lower bound for pruning.
--
--   **Formalization Note** "A dual of (5) is given by (20)" with optimal variables (23) is formalized as weak duality over all dual points together with equality of the dual value at $(\alpha^*,\gamma^*)$ and the primal value at $\beta^*$; this is strong duality with an explicit maximizer. Uniqueness of the dual optimum is not claimed. sign is `Real.sign` ($\mathrm{sign}(0)=0$), which is never evaluated at $0$ on an index with $|\beta^*_i|=M$. Optimality of $\beta^*$ is a hypothesis.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, pp. 13–14, Theorem 2, (20)–(24); pp. 30–31, Proof of Theorem 2

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

namespace L0BnB.Duality

/-- Theorem 2, pp. 13–14. Let `β*` be an optimal solution of (5) and `r* = y − Xβ*`.
1. If `√(λ₀/λ₂) ≤ M`, then (20) is a dual of (5): `h₁(α, γ) ≤ L0BnB.Reduced.F(β)` for all `α ∈ ℝⁿ`, `γ ∈ ℝᵖ`
   and all `β` feasible for (5); and the dual variables (23), `α* = −r*`,
   `γ*ᵢ = 𝟙[|β*ᵢ| = M](α*ᵀXᵢ − 2Mλ₂ sign(α*ᵀXᵢ))`, are optimal: `h₁(α*, γ*) = L0BnB.Reduced.F(β*)`.
2. If `√(λ₀/λ₂) > M`, then (22) is a dual of (5): `h₂(ρ, μ) ≤ L0BnB.Reduced.F(β)` for all `(ρ, μ)` feasible
   for (22) and all `β` feasible for (5); and the dual variables (24), `ρ* = −r*`,
   `μ*ᵢ = 𝟙[|β*ᵢ| = M](|ρ*ᵀXᵢ| − λ₀/M − λ₂M)`, are feasible for (22) and optimal:
   `h₂(ρ*, μ*) = L0BnB.Reduced.F(β*)`. -/
theorem theorem_2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (βs : Fin p → ℝ) (hβs : βs ∈ L0BnB.Reduced.box p M)
    (hopt : ∀ β ∈ L0BnB.Reduced.box p M, L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      (∀ (α : Fin n → ℝ) (γ : Fin p → ℝ), ∀ β ∈ L0BnB.Reduced.box p M,
        h1 X y lam0 lam2 M α γ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) ∧
      h1 X y lam0 lam2 M (alphaStar X y βs) (gammaStar X y lam2 M βs) =
        L0BnB.Reduced.F X y lam0 lam2 M βs) ∧
    (M < Real.sqrt (lam0 / lam2) →
      (∀ (ρ : Fin n → ℝ) (μ : Fin p → ℝ), Feas22 X lam0 lam2 M ρ μ → ∀ β ∈ L0BnB.Reduced.box p M,
        h2 y M ρ μ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) ∧
      Feas22 X lam0 lam2 M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) ∧
      h2 y M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) = L0BnB.Reduced.F X y lam0 lam2 M βs) := by sorry

end L0BnB.Duality
