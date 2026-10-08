-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_20
-- name    : NoisyMC.Convex.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:50.774767+00:00
-- url     : https://prove2.me/theorems/a2c9183f-24a7-463f-b89d-e1207d9dfb7f
-- title:
--   Lemma 20 — balancing the factors of an SVD: ‖Σ_Q − Σ_Q^{-1}‖_F ≤ ‖XᵀX − YᵀY‖_F/σ_min(Σ)
-- statement:
--   Let $X,Y\in\mathbb R^{n\times r}$ with $r\ge1$, and let $U\Sigma V^\top$ be a rank-$r$ singular value decomposition of $XY^\top$: $U,V\in\mathbb R^{n\times r}$ have orthonormal columns and $\Sigma=\mathrm{diag}(\sigma_1,\dots,\sigma_r)$ with $\sigma_k>0$. Then there is an invertible matrix $Q\in\mathbb R^{r\times r}$ such that
--
--   $$X=U\Sigma^{1/2}Q,\qquad Y=V\Sigma^{1/2}Q^{-\top},$$
--
--   and, writing $U_Q\Sigma_QV_Q^\top$ for the SVD of $Q$,
--
--   $$\|\Sigma_Q-\Sigma_Q^{-1}\|_F\le\frac1{\sigma_{\min}(\Sigma)}\,\|X^\top X-Y^\top Y\|_F.\qquad(140)$$
--
--   Moreover, if $X$ and $Y$ have balanced scale, $X^\top X=Y^\top Y$, then $Q$ is orthogonal.
--
--   The lemma measures how far a factorization $XY^\top$ is from the balanced one $U\Sigma^{1/2},V\Sigma^{1/2}$ by the imbalance $X^\top X-Y^\top Y$. It is used in Claim 3, where the gradient of the regularized objective controls this imbalance.
--
--   **Formalization Note.** Since $Q-Q^{-\top}=U_Q(\Sigma_Q-\Sigma_Q^{-1})V_Q^\top$ and the Frobenius norm is orthogonally invariant, $\|\Sigma_Q-\Sigma_Q^{-1}\|_F$ is stated as $\|Q-(Q^{-1})^\top\|_F$. The paper says "rotation matrix"; its proof produces $Q=U_QV_Q^\top$, which is orthogonal but may have determinant $-1$, so the conclusion is $Q^\top Q=I$.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 62, Lemma 20, (140)

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 20 (p. 62). Let `U Σ Vᵀ` be the SVD of the rank-`r` matrix `X Yᵀ`, `X, Y ∈ ℝ^{n×r}`.
There is an invertible `Q ∈ ℝ^{r×r}` with `X = U Σ^{1/2} Q` and `Y = V Σ^{1/2} Q^{-ᵀ}` and
`‖Σ_Q − Σ_Q^{-1}‖_F ≤ ‖XᵀX − YᵀY‖_F / σ_min(Σ)` (140), where `Σ_Q` holds the singular values of
`Q`; `‖Σ_Q − Σ_Q^{-1}‖_F = ‖Q − Q^{-ᵀ}‖_F` by orthogonal invariance. If `XᵀX = YᵀY`, then `Q` is
orthogonal. -/
theorem lemma_20 {n r : ℕ} (hr : 1 ≤ r) (X Y : RealMatrix n r) (S : SVD (X * Y.transpose) r) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ,
      IsUnit Q.det ∧
      X = svdU S * svdSigmaSqrt S * Q ∧
      Y = svdV S * svdSigmaSqrt S * (Q⁻¹).transpose ∧
      frobeniusNorm (Q - (Q⁻¹).transpose) ≤
        1 / sigmaMin S * frobeniusNorm (X.transpose * X - Y.transpose * Y) ∧
      (X.transpose * X - Y.transpose * Y = 0 → Q ∈ Matrix.orthogonalGroup (Fin r) ℝ) := by sorry

end NoisyMC.Convex
