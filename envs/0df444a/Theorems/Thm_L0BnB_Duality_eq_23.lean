-- Prove2me | Theorems.Thm_L0BnB_Duality_eq_23
-- name    : L0BnB.Duality.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:51.157578+00:00
-- url     : https://prove2.me/theorems/c1e37b82-29b5-47c4-9585-edf56761f787
-- title:
--   (23) — $\alpha^*=-r^*$, $\gamma^*$ are optimal for the dual (20)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M>0$ with $\sqrt{\lambda_0/\lambda_2}\le M$. Let $\beta^*$ be an optimal solution of the reduced relaxation (5): $\|\beta^*\|_\infty\le M$ and $F(\beta^*)\le F(\beta)$ whenever $\|\beta\|_\infty\le M$. Put $r^*=y-X\beta^*$ and
--
--   $$
--   \alpha^*=-r^*,\qquad \gamma^*_i=\mathbb 1_{[|\beta^*_i|=M]}\big(\alpha^{*T}X_i-2M\lambda_2\,\mathrm{sign}(\alpha^{*T}X_i)\big),\quad i\in[p].
--   $$
--
--   Then
--   $$ h_1(\alpha^*,\gamma^*)=F(\beta^*). $$
--
--   Together with weak duality this says that $(\alpha^*,\gamma^*)$ is an optimal solution of the dual (20) and that there is no duality gap. The paper's dual bounds of §3.2 are built by imitating this choice at an inexact primal solution.
--
--   **Formalization Note** sign is `Real.sign` with $\mathrm{sign}(0)=0$; the paper allows $\mathrm{sign}(0)\in[-1,1]$, but at an index with $|\beta^*_i|=M$ optimality forces $|\alpha^{*T}X_i|\ge 2M\lambda_2>0$, so the convention is never used. Optimality of $\beta^*$ is a hypothesis; existence of a minimizer is not assumed.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 14, Theorem 2, (23); p. 31, Proof of Theorem 2

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

namespace L0BnB.Duality

/-- (23), Theorem 2, p. 14 (proof p. 31). Let `√(λ₀/λ₂) ≤ M` and let `β*` be an optimal solution
of (5). With `r* = y − Xβ*`, the dual variables `α* = −r*` and
`γ*ᵢ = 𝟙[|β*ᵢ| = M](α*ᵀXᵢ − 2Mλ₂ sign(α*ᵀXᵢ))` attain the optimal value of (5):
`h₁(α*, γ*) = L0BnB.Reduced.F(β*)`. -/
theorem eq_23 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M)
    (βs : Fin p → ℝ) (hβs : βs ∈ L0BnB.Reduced.box p M)
    (hopt : ∀ β ∈ L0BnB.Reduced.box p M, L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    h1 X y lam0 lam2 M (alphaStar X y βs) (gammaStar X y lam2 M βs) = L0BnB.Reduced.F X y lam0 lam2 M βs := by sorry

end L0BnB.Duality
