-- Prove2me | Theorems.Thm_IRLSM_Convergence_eq_6_11
-- name    : IRLSM.Convergence.eq_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:37.233685+00:00
-- url     : https://prove2.me/theorems/53e2040a-98b5-4edd-88e7-abdec81e0d68
-- title:
--   (6.11) — $\|X\|_*\le\mathcal J_\varepsilon(X)\le\|X\|_*+n\varepsilon$, hence $\|\bar X\|_*-\|X\|_*\le n\varepsilon$ for a minimizer $\bar X$ of $\mathcal J_\varepsilon$
-- statement:
--   Let $\varepsilon>0$. For every $n\times p$ matrix $Y$,
--   $$\|Y\|_*\le\mathcal J_\varepsilon(Y)\le\|Y\|_*+n\varepsilon .$$
--   Consequently, for any matrix $X$ with $\mathcal S(X)=\mathscr M$ and any minimizer $\bar X$ of $\mathcal J_\varepsilon$ subject to $\mathcal S(\bar X)=\mathscr M$,
--   $$\|\bar X\|_*-\|X\|_*\le n\varepsilon .\tag{6.11}$$
--
--   This bound compares the smoothed problem with nuclear norm minimization and feeds the error estimate of Theorem 6.11(ii).
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. $n\le p$ makes the nuclear norm the sum of the $n$ singular values that $\mathcal J_\varepsilon$ smooths.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Theorem 6.11(ii), (6.11), p. 22

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **The bound (6.11).** Let `ε > 0`. For every `Y`, `‖Y‖_* ≤ 𝒥_ε(Y) ≤ ‖Y‖_* + nε`; consequently,
for any feasible `X` (`S(X) = 𝓜`) and any minimizer `X̄` of `𝒥_ε` subject to `S(X̄) = 𝓜`,
`‖X̄‖_* − ‖X‖_* ≤ nε`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Theorem 6.11(ii), (6.11), p. 22.

Formalization Notes: real matrices. `n ≤ p` is the page's standing assumption (p. 4): it makes
`‖Y‖_*` (a sum over the `p` entries of `singularValues`) the sum of the `n` singular values that
`𝒥_ε` smooths. The sandwich is the chain displayed just before (6.11). -/
theorem eq_6_11 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (ε : ℝ)
    (hnp : n ≤ p) (hε : 0 < ε) :
    (∀ Y : Matrix (Fin n) (Fin p) ℝ,
      nuclearNorm Y ≤ Jeps ε Y ∧ Jeps ε Y ≤ nuclearNorm Y + n * ε) ∧
    ∀ Xbar X : Matrix (Fin n) (Fin p) ℝ, observationOp A Xbar = M →
      (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps ε Xbar ≤ Jeps ε Y) →
      observationOp A X = M → nuclearNorm Xbar - nuclearNorm X ≤ n * ε := by sorry

end IRLSM.Convergence
