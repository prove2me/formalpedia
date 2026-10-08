-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_2
-- name    : NoisyMC.Convex.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:03.826078+00:00
-- url     : https://prove2.me/theorems/b9d3153c-fcf6-452e-b504-fcef9206e04b
-- title:
--   Lemma 2 — an approximate critical point of the factored objective is within 2304·κ‖∇f‖_F/(c_inj√σ_min) of every minimizer of (3)
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $M=M^\star+E$ where $M^\star\in\mathbb R^{n\times n}$ has rank $r\ge1$, extreme singular values $\sigma_{\max},\sigma_{\min}$ and condition number $\kappa=\sigma_{\max}/\sigma_{\min}$; let $\Omega$ be an index set, $0<p\le1$, $\lambda>0$ and $c_{\rm inj}>0$. Suppose $X,Y\in\mathbb R^{n\times r}$ satisfy
--
--   1. every singular value of $X$ and of $Y$ lies in $[\sqrt{\sigma_{\min}/2},\sqrt{2\sigma_{\max}}]$;
--   2. Condition 1: $\|\mathcal P_\Omega(E)\|<\lambda/8$ and $\|\mathcal P_\Omega(XY^\top-M^\star)-p(XY^\top-M^\star)\|<\lambda/8$;
--   3. Condition 2: $p^{-1}\|\mathcal P_\Omega(H)\|_F^2\ge c_{\rm inj}\|H\|_F^2$ for every $H$ in the tangent space of $XY^\top$;
--   4. the small-gradient condition $\|\nabla f(X,Y)\|_F\le c\,\frac{\sqrt{c_{\rm inj}p}}{\kappa}\cdot\frac\lambda p\sqrt{\sigma_{\min}}$ (23), where $f$ is the objective (17).
--
--   Then every minimizer $Z_{\rm cvx}$ of the convex program (3) satisfies
--
--   $$\|XY^\top-Z_{\rm cvx}\|_F\le2304\,\frac{\kappa}{c_{\rm inj}}\,\frac1{\sqrt{\sigma_{\min}}}\,\|\nabla f(X,Y)\|_F.\qquad(24)$$
--
--   This is the deterministic bridge of the paper: a point with nearly vanishing nonconvex gradient pins down every solution of the convex program, even though (3) need not have a unique minimizer.
--
--   **Formalization Note.** The paper states (24) with "$\lesssim$". The constant $2304=32\cdot72$ is the one its proof yields (p. 28): combining (61), $\frac{c_{\rm inj}}{32}\|\Delta\|_F^2\le\frac1{2p}\|\mathcal P_\Omega(\Delta)\|_F^2$, with (60), $\frac1{2p}\|\mathcal P_\Omega(\Delta)\|_F^2\le72\kappa\frac1{\sqrt{\sigma_{\min}}}\|\nabla f\|_F\|\Delta\|_F$. The "sufficiently small" $c$ is existential and comes before all data. The singular-value condition is written as $\frac{\sigma_{\min}}2\|v\|^2\le\|Xv\|^2\le2\sigma_{\max}\|v\|^2$ for all $v\in\mathbb R^r$. $\lambda>0$ is implicit in the paper (its proof divides by $\lambda$). The fact $c_{\rm inj}\le1/p$ is derived in the proof, not assumed.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 12, Lemma 2, (23)–(24); constant from the proof, pp. 27–28, (60)–(61)

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 2 (p. 12). There is an absolute constant `c > 0` such that the following holds. Let
`M = M⋆ + E` with `M⋆` of rank `r` (SVD `S`; `σ_max, σ_min, κ` its extreme singular values and
condition number), `0 < p ≤ 1`, `λ > 0`, `c_inj > 0`. Let `X, Y ∈ ℝ^{n×r}` have all singular
values in `[√(σ_min/2), √(2σ_max)]`, satisfy Conditions 1 and 2 and the small-gradient condition
(23) `‖∇f(X,Y)‖_F ≤ c (√(c_inj p)/κ) (λ/p) √σ_min`. Then every minimizer `Z_cvx` of (3) obeys
(24) with the explicit constant of the proof (p. 28, 2304 = 32·72):
`‖X Yᵀ − Z_cvx‖_F ≤ 2304 · κ/(c_inj √σ_min) · ‖∇f(X,Y)‖_F`. -/
theorem lemma_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n r : ℕ}, 1 ≤ r →
      ∀ (Mstar Emat : RealMatrix n n) (S : SVD Mstar r) (Ω : Finset (Fin n × Fin n))
        (p lam cinj : ℝ), 0 < p → p ≤ 1 → 0 < lam → 0 < cinj →
      ∀ X Y : RealMatrix n r,
        SingularValuesIn X (sigmaMin S / 2) (2 * sigmaMax S) →
        SingularValuesIn Y (sigmaMin S / 2) (2 * sigmaMax S) →
        Condition1 Ω Mstar Emat p lam X Y → Condition2 Ω p cinj X Y →
        gradNorm Ω (Mstar + Emat) lam p X Y ≤
          c * (Real.sqrt (cinj * p) / condNum S) * (lam / p) * Real.sqrt (sigmaMin S) →
      ∀ Z : RealMatrix n n, IsCvxMinimizer Ω (Mstar + Emat) lam Z →
        frobeniusNorm (X * Y.transpose - Z) ≤
          2304 * condNum S / (cinj * Real.sqrt (sigmaMin S)) *
            gradNorm Ω (Mstar + Emat) lam p X Y := by sorry

end NoisyMC.Convex
