-- Prove2me | Theorems.Thm_IRLSM_Convergence_theorem_7_1
-- name    : IRLSM.Convergence.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:55.111989+00:00
-- url     : https://prove2.me/theorems/d17c86af-952c-4ba1-ad22-718fbe211e85
-- title:
--   Theorem 7.1 — Weyl's bound $|\sigma_i(X)-\sigma_i(Y)|\le\|X-Y\|_F$
-- statement:
--   Let $X,Y$ be real $n\times p$ matrices. Then for every $i=1,2,\dots$
--   $$|\sigma_i(X)-\sigma_i(Y)|\le\|X-Y\|_F .$$
--
--   Singular values are therefore 1-Lipschitz in the Frobenius norm; the convergence proof uses this to pass $\sigma_{K+1}$ to the limit along subsequences.
--
--   **Formalization Note** Real matrices. `sv X i` is $\sigma_{i+1}(X)$ (0-based) and equals $0$ for $i\ge p$, so every index of the page is covered. This statement is also posed elsewhere on the platform in another encoding of the singular values.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Theorem 7.1, p. 23

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Theorem 7.1 (Weyl).** For `X, Y ∈ M_{n×p}` and every `i = 1, 2, …`,
`|σ_i(X) − σ_i(Y)| ≤ ‖X − Y‖_F`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Theorem 7.1, p. 23.

Formalization Notes: real matrices; `sv X i` is the page's `σ_{i+1}(X)` (0-based), and is `0` for
`i ≥ p`, so every index of the page is covered. -/
theorem theorem_7_1 {n p : ℕ} (X Y : Matrix (Fin n) (Fin p) ℝ) :
    ∀ i : ℕ, |sv X i - sv Y i| ≤ frobeniusNorm (X - Y) := by sorry

end IRLSM.Convergence
