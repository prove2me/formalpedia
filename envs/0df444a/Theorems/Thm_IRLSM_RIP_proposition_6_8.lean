-- Prove2me | Theorems.Thm_IRLSM_RIP_proposition_6_8
-- name    : IRLSM.RIP.proposition_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:39.648477+00:00
-- url     : https://prove2.me/theorems/58fc67af-dc56-448c-b19b-b86d1a12569e
-- title:
--   Proposition 6.8 — δ_4k < √2 − 1 implies the strong rank null space property of order k with η = √2 δ_4k/(1 − δ_3k)
-- statement:
--   Let $\mathcal S : \mathbb R^{n\times p}\to\mathbb R^m$ be a linear map whose rank restricted isometry constants (Definition 1.1) satisfy $\delta_{4k} > 0$ and
--   $$
--   \delta_{4k} < \sqrt 2 - 1 \approx 0.41 .
--   $$
--   Then $\mathcal S$ satisfies the strong rank null space property of order $k$ (Definition 6.4) with constant
--   $$
--   \eta = \sqrt 2\,\frac{\delta_{4k}}{1 - \delta_{3k}} \in (0,1).
--   $$
--   That is, for every nonzero $X$ in the kernel of $\mathcal S$ and every decomposition $X = X_1 + X_2$ with $\operatorname{rank}X_1 \le k$, there are $H_1, H_2$ with $X = H_1 + H_2$, $\operatorname{rank}H_1 \le 2k$, $\langle H_1, H_2\rangle = 0$, $X_1H_2^{\top} = 0$, $X_1^{\top}H_2 = 0$ and $\|H_1\|_* \le \eta\|H_2\|_*$.
--
--   Together with the convergence analysis of the IRLS-M algorithm, this shows that the algorithm recovers every matrix of rank at most $k$ from measurements with a small restricted isometry constant, and that nuclear-norm minimization does so stably.
--
--   **Formalization Note.** Real matrices; $\mathcal S(X)_\ell = \langle A_\ell, X\rangle$. $\delta_k$ is the squared-form constant of Definition 1.1, defined for every $k$ (here $4k$ may exceed $n$). The hypothesis $\delta_{4k} > 0$ is Definition 1.1's own requirement $\delta_k > 0$; without it $\eta$ could be $0 \notin (0,1)$. The conclusion includes $\eta \in (0,1)$, which is part of Definition 6.4.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Proposition 6.8 with (6.6), p. 18; proof pp. 19–20

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- Proposition 6.8: if the rank restricted isometry constant satisfies `δ_{4k} < √2 − 1`, then
`S` has the strong rank null space property of order `k` with constant
`η = √2 δ_{4k}/(1 − δ_{3k}) ∈ (0, 1)`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Proposition 6.8 with (6.6), p. 18.

Formalization Notes: real matrices; `S(X)_l = ⟨A_l, X⟩`; `δ_k` is `ripConst A k` (squared form
of Definition 1.1, defined for every `k`, since `4k` may exceed `n`). The hypothesis
`0 < δ_{4k}` is the positivity "δ_k > 0" of Definition 1.1; without it `η` could be
`0 ∉ (0, 1)`. `SRNSP` contains `0 < η < 1`, so the conclusion includes "η ∈ (0, 1)". -/
theorem proposition_6_8 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < IRLSM.Convergence.ripConst A (4 * k)) (h66 : IRLSM.Convergence.ripConst A (4 * k) < Real.sqrt 2 - 1) :
    IRLSM.Convergence.SRNSP A k (Real.sqrt 2 * IRLSM.Convergence.ripConst A (4 * k) / (1 - IRLSM.Convergence.ripConst A (3 * k))) := by sorry

end IRLSM.RIP
