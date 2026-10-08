-- Prove2me | Theorems.Thm_IRLSM_Convergence_rho_attained
-- name    : IRLSM.Convergence.rho_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:50.281626+00:00
-- url     : https://prove2.me/theorems/cd8ebaec-a72a-4c4f-9f5f-68722d30f088
-- title:
--   §6.2 — $\rho_k(X)_*$ is attained at the $k$-spectral truncation: $\rho_k(X)_*=\sum_{i>k}\sigma_i(X)$
-- statement:
--   Let $X$ be a real $n\times p$ matrix and $k\in\mathbb N$. The best $k$-rank approximation error in the nuclear norm,
--   $$\rho_k(X)_*=\min_{\operatorname{rank}Z\le k}\|X-Z\|_*,$$
--   is attained at the $k$-spectral truncation $Z=X_{[k]}$, so that
--   $$\rho_k(X)_*=\|X-X_{[k]}\|_*=\sum_{i>k}\sigma_i(X).$$
--
--   This identifies the error term of the recovery bounds (Lemma 6.6, Corollary 6.7, Theorem 6.11) with a tail sum of singular values.
--
--   **Formalization Note** Real matrices. $\rho_k$ is defined as an infimum; the statement asserts that it equals the tail sum $\sum_{i>k}\sigma_i(X)$ (`tailSingularSum X k`, 0-based index $\ge k$) and that some $Z$ of rank at most $k$ attains it.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), §6.2, p. 17, sentence after the definition of ρ_k

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Best rank-`k` approximation in the nuclear norm.** `ρ_k(X)_* = min_{rank Z ≤ k} ‖X − Z‖_*`
is attained at the `k`-spectral truncation `X_[k]`, so it equals `‖X − X_[k]‖_* = Σ_{i > k} σ_i(X)`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, §6.2, p. 17 (sentence after the definition of `ρ_k`).

Formalization Notes: real matrices. `‖X − X_[k]‖_*` is written as `tailSingularSum X k`, the sum
of the singular values with 0-based index `≥ k` (the page's `σ_{k+1}, σ_{k+2}, …`); this is its
value for every SVD defining `X_[k]`. The minimum is stated as: the infimum `ρ_k` equals that tail
sum, and some `Z` of rank `≤ k` attains it. -/
theorem rho_attained {n p : ℕ} (k : ℕ) (X : Matrix (Fin n) (Fin p) ℝ) :
    rho k X = tailSingularSum X k ∧
      ∃ Z : Matrix (Fin n) (Fin p) ℝ, Z.rank ≤ k ∧ nuclearNorm (X - Z) = rho k X := by sorry

end IRLSM.Convergence
