-- Prove2me | Theorems.Thm_L0BnB_Duality_eq_24
-- name    : L0BnB.Duality.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:42.298358+00:00
-- url     : https://prove2.me/theorems/fc3682de-bd4e-4925-b0c4-d3576e514f2a
-- title:
--   (24) — $\rho^*=-r^*$, $\mu^*$ are feasible and optimal for the dual (22)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M>0$ with $\sqrt{\lambda_0/\lambda_2}>M$. Let $\beta^*$ be an optimal solution of the reduced relaxation (5), put $r^*=y-X\beta^*$ and
--
--   $$
--   \rho^*=-r^*,\qquad \mu^*_i=\mathbb 1_{[|\beta^*_i|=M]}\big(|\rho^{*T}X_i|-\lambda_0/M-\lambda_2M\big),\quad i\in[p].
--   $$
--
--   Then $(\rho^*,\mu^*)$ is feasible for (22), that is $|\rho^{*T}X_i|-\mu^*_i\le\lambda_0/M+\lambda_2M$ for every $i$, and
--
--   $$ h_2(\rho^*,\mu^*)=F(\beta^*). $$
--
--   Together with weak duality this says that $(\rho^*,\mu^*)$ is an optimal solution of (22) with no duality gap. The paper omits this proof ("follows along the lines similar to what was shown above").
--
--   **Formalization Note** Optimality of $\beta^*$ is a hypothesis; existence of a minimizer is not assumed.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 14, Theorem 2, (24); p. 31, Proof of Theorem 2, case √(λ0/λ2) > M

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

namespace L0BnB.Duality

/-- (24), Theorem 2, p. 14. Let `√(λ₀/λ₂) > M` and let `β*` be an optimal solution of (5). With
`r* = y − Xβ*`, the dual variables `ρ* = −r*` and `μ*ᵢ = 𝟙[|β*ᵢ| = M](|ρ*ᵀXᵢ| − λ₀/M − λ₂M)`
are feasible for (22) and attain the optimal value of (5): `h₂(ρ*, μ*) = L0BnB.Reduced.F(β*)`. -/
theorem eq_24 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs : βs ∈ L0BnB.Reduced.box p M)
    (hopt : ∀ β ∈ L0BnB.Reduced.box p M, L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    Feas22 X lam0 lam2 M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) ∧
      h2 y M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) = L0BnB.Reduced.F X y lam0 lam2 M βs := by sorry

end L0BnB.Duality
