-- Prove2me | Theorems.Thm_HolisticService_Effort_hessian_minors
-- name    : HolisticService.Effort.hessian_minors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:45.096245+00:00
-- url     : https://prove2.me/theorems/bbbeffee-608c-4261-83a1-3a91955d7122
-- title:
--   Proof of Proposition 1, p. 26 — Hessian of Ũ and its leading principal minors |Hᵢ| = (−1)ⁱ rⁱ Π (σᴴⱼ − σᴸⱼ)² |P[1:i;1:i]|
-- statement:
--   Assume the standing assumptions of the service design model. Then:
--
--   1. For every effort vector $\delta$ and steps $i,j$, the second partial derivative of $\tilde{\mathcal U}$ is
--   $$\frac{\partial^2\tilde{\mathcal U}}{\partial\delta_i\,\partial\delta_j}(\delta) = -r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)\rho_{i,j}$$
--   (with $\rho_{i,i} = 1$); call $\boldsymbol H_n$ the matrix of these entries.
--
--   2. For $0 \le k \le n$, the $k$-th leading principal minor of $\boldsymbol H_n$ is
--   $$|\boldsymbol H_k| = (-1)^k r^k \prod_{j=1}^k(\sigma^H_j-\sigma^L_j)^2\,|\mathbf P[1:k;1:k]|,$$
--   and $(-1)^k|\boldsymbol H_k| > 0$ for $1 \le k \le n$.
--
--   The alternating signs of the leading principal minors are the paper's argument that $\tilde{\mathcal U}$ is strictly concave.
--
--   **Formalization Note** The leading block of size $k$ is the first $k$ steps in the 0-based order (`Fin.castLE`), which are the paper's steps $1,\dots,k$. The second partial is written as the derivative in $\delta_j$ of the derivative in $\delta_i$, each along one coordinate with the others fixed.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 26 (PDF 26), proof of Proposition 1, Hessian H_n and minors |H_i|

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 1, p. 26: the second partial derivatives of `Ũ` are the entries
`−r(σ^H_i − σ^L_i)(σ^H_j − σ^L_j)ρ_{i,j}` of `hessU`, and the leading principal minors are
`|H_k| = (−1)^k r^k Π_{j≤k} (σ^H_j − σ^L_j)² |P[1:k;1:k]|`, with `(−1)^k |H_k| > 0` for `1 ≤ k ≤ n`.
Steps are 0-based: the leading block `Fin k` (via `Fin.castLE`) is the paper's steps `1, …, k`. -/
theorem hessian_minors {n : ℕ} (M : Params n) (hS : M.Standing) :
    (∀ (δ : Fin n → ℝ) (i j : Fin n),
      deriv (fun s => deriv (fun t => Utilde M (Function.update (Function.update δ j s) i t))
        (Function.update δ j s i)) (δ j) = hessU M i j) ∧
    ∀ (k : ℕ) (hk : k ≤ n),
      ((hessU M).submatrix (Fin.castLE hk) (Fin.castLE hk)).det
          = (-1) ^ k * M.r ^ k
            * (∏ j : Fin k, (M.sH (Fin.castLE hk j) - M.sL (Fin.castLE hk j)) ^ 2)
            * (M.P.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∧
        (1 ≤ k → 0 < (-1) ^ k * ((hessU M).submatrix (Fin.castLE hk) (Fin.castLE hk)).det) := by sorry

end HolisticService.Effort
