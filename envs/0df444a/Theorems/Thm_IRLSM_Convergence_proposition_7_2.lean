-- Prove2me | Theorems.Thm_IRLSM_Convergence_proposition_7_2
-- name    : IRLSM.Convergence.proposition_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:11.914437+00:00
-- url     : https://prove2.me/theorems/9815883f-68c8-4a60-92f7-5d67f44805bb
-- title:
--   Proposition 7.2 — $|\|X-X_{[j]}\|_*-\|Y-Y_{[j]}\|_*|\le\|X-Y\|_*$ and $(J-j)\sigma_J(X)\le\|X-Y\|_*+\|Y-Y_{[j]}\|_*$
-- statement:
--   Let $X,Y$ be real $n\times p$ matrices. For every $j\in\mathbb N$,
--   $$\big|\|X-X_{[j]}\|_*-\|Y-Y_{[j]}\|_*\big|\le\|X-Y\|_*,$$
--   and for every $J>j$,
--   $$(J-j)\,\sigma_J(X)\le\|X-Y\|_*+\|Y-Y_{[j]}\|_* .$$
--   Here $X_{[j]}$ is the $j$-spectral truncation, so $\|X-X_{[j]}\|_*=\sum_{i>j}\sigma_i(X)$.
--
--   The second inequality bounds a single singular value of $X$ by the distance to $Y$ and the tail of $Y$; it is the step of Theorem 6.11(ii) that controls $n\varepsilon$.
--
--   **Formalization Note** Real matrices. $\|X-X_{[j]}\|_*$ is the tail sum $\sum_{i>j}\sigma_i(X)$, its value for every SVD defining $X_{[j]}$. $\sigma_J(X)$ is `sv X (J - 1)` (0-based; $J\ge1$ since $J>j\ge0$); $J-j$ is computed in $\mathbb R$.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Proposition 7.2, p. 23

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Proposition 7.2.** For `X, Y ∈ M_{n×p}` and every `j`,
`|‖X − X_[j]‖_* − ‖Y − Y_[j]‖_*| ≤ ‖X − Y‖_*`, and for every `J > j`,
`(J − j) σ_J(X) ≤ ‖X − Y‖_* + ‖Y − Y_[j]‖_*`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Proposition 7.2, p. 23.

Formalization Notes: real matrices. `‖X − X_[j]‖_*` is `tailSingularSum X j`, the sum of the
singular values `σ_{j+1}, σ_{j+2}, …`; this is its value whichever SVD defines `X_[j]`. `σ_J(X)` is
the 0-based `sv X (J - 1)`; since `J > j ≥ 0`, `J ≥ 1` and the natural subtraction is exact.
`J − j` is computed in `ℝ`. -/
theorem proposition_7_2 {n p : ℕ} (X Y : Matrix (Fin n) (Fin p) ℝ) :
    ∀ j : ℕ, |tailSingularSum X j - tailSingularSum Y j| ≤ nuclearNorm (X - Y) ∧
      ∀ J : ℕ, j < J →
        ((J : ℝ) - j) * sv X (J - 1) ≤ nuclearNorm (X - Y) + tailSingularSum Y j := by sorry

end IRLSM.Convergence
