-- Prove2me | Theorems.Thm_LatentRobust_pinv_sqrt_opNorm
-- name    : LatentRobust.pinv_sqrt_opNorm
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:53.516759+00:00
-- url     : https://prove2.me/theorems/dedcd477-e965-4fd6-a8f6-56061552a7be
-- title:
--   App. A.3, p.22 — $\|\Sigma^{\dagger1/2}\|=1/\sigma_{\min}(W)$
-- statement:
--   Let $W\in\mathbb R^{d\times k}$ have full column rank with $k\ge1$, and let $\Sigma=WW^\top$. Then
--   $$
--   \big\|\Sigma^{\dagger\,1/2}\big\|=\frac{1}{\sigma_{\min}(W)},
--   $$
--   where $\|\cdot\|$ is the operator norm from $\ell_2$ to $\ell_2$, $\Sigma^{\dagger\,1/2}$ is the positive semidefinite square root of the Moore–Penrose inverse $\Sigma^\dagger$, and $\sigma_{\min}(W)$ is the smallest nonzero singular value of $W$.
--
--   It converts the bound (19) into the bound in terms of $\sigma_{\min}(W)$ that appears in condition (7).
--
--   Differences from the source:
--   - generalization: W ∈ ℝ^{d×k} tall (k < d) → any d and k with W of full column rank (no k < d); reason: no step uses k < d; the statement for every d specializes to tall W
--   - reading: latent vector z ∈ ℝ^k → 1 ≤ k; reason: the latent dimension is a positive integer; σ_min(W), the smallest nonzero singular value, does not exist for k = 0
--   - encoding: ‖Σ†^{1/2}‖ → the ℓ2 → ℓ2 operator norm of the matrix acting on Euclidean space; reason: the paper's ‖·‖ of a matrix is the operator norm (p.4)
--   - encoding: Σ†^{1/2} → cfc Real.sqrt Σ† (continuous functional calculus of the symmetric matrix Σ†); reason: Σ† is symmetric positive semidefinite, so this is its positive semidefinite square root
--   - encoding: the Moore–Penrose inverse † → pinv, the matrix satisfying the four Penrose conditions (chosen by Classical.epsilon); reason: the Penrose conditions determine A† uniquely and it exists for every real matrix
--   - encoding: σ_min(W), the smallest nonzero singular value → the singular value of index k − 1 (zero-based, decreasing) of W acting ℝ^k → ℝ^d; reason: for W of full column rank with k ≥ 1 all k singular values are positive, so this is the smallest nonzero one
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3 (proof of Theorem 3.1), p.22, "by using ∥Σ†1/2∥= 1/σmin(W)"

import Mathlib
import Definitions.Def_LatentRobust_pinv
import Definitions.Def_LatentRobust_sigmaMin

namespace LatentRobust

/-- **`‖Σ†^{1/2}‖ = 1/σ_min(W)`** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.22): for a `d × k` matrix `W` of
full column rank (`k ≥ 1`) and `Σ = WWᵀ`, the operator norm of `Σ†^{1/2}` is
`1/σ_min(W)`.

**Formalization Note** The norm is the `ℓ2 → ℓ2` operator norm of the matrix acting on
Euclidean space (`toEuclideanLin`), not Mathlib's default entrywise matrix norm. `Σ†^{1/2}` is
`cfc Real.sqrt Σ†`, `†` is `pinv`, and `σ_min` is `sigmaMin`. -/
theorem pinv_sqrt_opNorm {d k : ℕ} (W : Matrix (Fin d) (Fin k) ℝ) (hk : 1 ≤ k)
    (hW : W.rank = k) :
    ‖LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (cfc Real.sqrt (pinv (W * W.transpose))))‖ =
      1 / sigmaMin W := by sorry

end LatentRobust
