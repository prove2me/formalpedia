-- Prove2me | Theorems.Thm_KLTNuclear_RankRecovery_projector_residual
-- name    : KLTNuclear.RankRecovery.projector_residual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:30.274838+00:00
-- url     : https://prove2.me/theorems/dbb9e527-0cc5-4737-abdb-845cb2ee4087
-- title:
--   Proof of (5.3), p. 20 — $\|\mathcal P(\hat A^{\lambda'}-\mathbf X)\|_2=\sqrt r\,\lambda'm_1m_2/2$ when $\hat r=r$
-- statement:
--   Consider the matrix completion data of the module `KLTNuclear.RankRecovery.Model` ($n,m_1,m_2\ge1$), the matrix $\mathbf X$, a parameter $\lambda>0$ and a minimizer $\hat A^\lambda$ of (3.1). Let
--   $$\mathbf X=\sum_{k=1}^{q}\sigma_k\,u_kv_k^\top$$
--   be a singular value decomposition of $\mathbf X$ ($\sigma_k>0$, $(u_k)$ and $(v_k)$ orthonormal) with $\sigma_1\ge\sigma_2\ge\dots\ge\sigma_q$, and for $r\in\mathbb N$ let $\mathcal P$ be the orthogonal projector onto the linear span of the matrices $u_kv_k^\top$, $k\le r$ (all $k\le q$ if $r>q$). If $\operatorname{rank}(\hat A^\lambda)=r$, then
--
--   $$\|\mathcal P(\hat A^\lambda-\mathbf X)\|_2=\sqrt r\,\frac{\lambda m_1m_2}{2}.$$
--
--   In the proof of (5.3) this is applied with parameter $\lambda'$ and $r=\operatorname{rank}(A_0)=\hat r$ (by (5.1) and (5.2)); it is the part of the estimation error that the shrinkage of the top $r$ singular values of $\mathbf X$ forces.
--
--   **Formalization Note** The projector is built from the same ordered singular value decomposition of $\mathbf X$ that (3.2) thresholds; it is `spanProjector` applied to the pairs $(u_k,v_k)$ with 0-based index $k<r$. The decomposition is carried as data (`SVD` with antitone `sigma`). The paper's statement has $\lambda'$ and $r=\operatorname{rank}(A_0)$; the Lean statement is for an arbitrary parameter and an arbitrary $r$ equal to $\hat r$, which contains the paper's case.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 20, proof of Theorem 8, (5.3) ('Here ‖𝒫(Â^λ′ − X)‖2 = √r λ′m1m2/2 in view of (3.2)')

import Mathlib
import Definitions.Def_KLTNuclear_RankRecovery_Model

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-- Proof of (5.3) (p. 20): let `𝐗 = Σ_k σ_k u_k v_kᵀ` be an SVD with decreasing singular values
and `𝒫` the projector onto the span of `u_k v_kᵀ`, `k < r` (0-based). If `rank(Â^λ) = r`, then
`‖𝒫(Â^λ − 𝐗)‖₂ = √r · λm₁m₂/2`. -/
theorem projector_residual {m₁ m₂ n : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator idx y lam Ahat)
    (q : ℕ) (S : SVD (bigX idx y) q) (hS : Antitone S.sigma)
    (r : ℕ) (hr : Ahat.rank = r) :
    frobeniusNorm (spanProjector (fun k : {k : Fin q // k.val < r} => S.u k.val)
        (fun k => S.v k.val) (Ahat - bigX idx y)) =
      Real.sqrt r * (lam * ((m₁ : ℝ) * m₂) / 2) := by sorry

end KLTNuclear.RankRecovery
