-- Prove2me | Theorems.Thm_NoisyMC_Convex_claim_2
-- name    : NoisyMC.Convex.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:45.754384+00:00
-- url     : https://prove2.me/theorems/b1a8077e-bbbc-4d5e-a588-f38b494061ca
-- title:
--   Claim 2 — residual decomposition at an approximate critical point: ‖P_T(R)‖_F ≤ 72κ p‖∇f‖_F/√σ_min and ‖P_{T⊥}(R)‖ < λ/2
-- statement:
--   There is an absolute constant $c>0$ with the following property. Work under the assumptions of Lemma 2 with this $c$: $M=M^\star+E$ with $M^\star$ of rank $r\ge1$ (extreme singular values $\sigma_{\max},\sigma_{\min}$, condition number $\kappa$), $0<p\le1$, $\lambda>0$, $c_{\rm inj}>0$, and $X,Y\in\mathbb R^{n\times r}$ with all singular values in $[\sqrt{\sigma_{\min}/2},\sqrt{2\sigma_{\max}}]$ satisfying Conditions 1 and 2 and the small-gradient condition (23). Let $U\Sigma V^\top$ be any SVD of $XY^\top$, let $T$ be the tangent space of $XY^\top$ with projections $\mathcal P_T$ and $\mathcal P_{T^\perp}$, and define $R$ by
--
--   $$\mathcal P_\Omega(XY^\top-M)=-\lambda UV^\top+R.\qquad(50)$$
--
--   Then
--
--   $$\|\mathcal P_T(R)\|_F\le72\kappa\,\frac p{\sqrt{\sigma_{\min}}}\,\|\nabla f(X,Y)\|_F\quad\text{and}\quad\|\mathcal P_{T^\perp}(R)\|<\lambda/2.\qquad(51)$$
--
--   The claim says that $\lambda^{-1}\mathcal P_\Omega(M-XY^\top)$ is close to a subgradient of the nuclear norm at $XY^\top$. This is how an approximate critical point of the nonconvex problem is compared with the minimizers of the convex program in Lemma 2.
--
--   **Formalization Note.** $R$ is defined as $\mathcal P_\Omega(XY^\top-M)+\lambda UV^\top$, so (50) holds by definition, and $UV^\top=\sum_ku_kv_k^\top$ is `signMatrix`. $\mathcal P_T$ and $\mathcal P_{T^\perp}$ are the published projections built from the same SVD. The constants 72 and $1/2$ are the paper's; the smallness constant $c$ is existential and placed before all data, because the paper's proof only fixes it through a "$\lesssim$" (p. 30, (75)).
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 26, Claim 2, (50)–(51)

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Claim 2 (p. 26). There is an absolute constant `c > 0` such that, under the assumptions of
Lemma 2 with this `c` in (23), for every SVD `U Σ Vᵀ` of `X Yᵀ` the residual
`R := P_Ω(X Yᵀ − M) + λ U Vᵀ` (so that `P_Ω(X Yᵀ − M) = −λ U Vᵀ + R`, (50)) satisfies (51):
`‖P_T(R)‖_F ≤ 72κ · p/√σ_min · ‖∇f(X,Y)‖_F` and `‖P_{T⊥}(R)‖ < λ/2`, with `T` the tangent space
of `X Yᵀ`. Here `M = M⋆ + E`, and `σ_max, σ_min, κ` are those of `M⋆`. -/
theorem claim_2 :
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
      ∀ SX : SVD (X * Y.transpose) r,
        frobeniusNorm (tangentProjection SX
            (samplingProjection Ω (X * Y.transpose - (Mstar + Emat)) + lam • signMatrix SX)) ≤
          72 * condNum S * (p / Real.sqrt (sigmaMin S)) * gradNorm Ω (Mstar + Emat) lam p X Y ∧
        spectralNorm (normalProjection SX
            (samplingProjection Ω (X * Y.transpose - (Mstar + Emat)) + lam • signMatrix SX)) <
          lam / 2 := by sorry

end NoisyMC.Convex
