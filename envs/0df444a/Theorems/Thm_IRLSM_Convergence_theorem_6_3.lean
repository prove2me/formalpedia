-- Prove2me | Theorems.Thm_IRLSM_Convergence_theorem_6_3
-- name    : IRLSM.Convergence.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:49.300953+00:00
-- url     : https://prove2.me/theorems/16605266-357b-49b4-800a-a13c265b2bb2
-- title:
--   Theorem 6.3 — exact recovery of all $k$-rank matrices by nuclear norm minimization $\iff$ RNSP of order $k$
-- statement:
--   Let $\mathcal S:\mathbb R^{n\times p}\to\mathbb R^m$ be linear and $k\in\mathbb N$. Then every $X$ of rank at most $k$ is the unique solution of
--   $$\min\|Y\|_*\quad\text{subject to}\quad\mathcal S(Y)=\mathcal S(X)\tag{6.3}$$
--   if and only if $\mathcal S$ satisfies the rank null space property of order $k$.
--
--   The rank null space property is thus exactly the condition for uniform exact recovery of low-rank matrices by nuclear norm minimization.
--
--   **Formalization Note** Real matrices; $\mathcal S$ is given by measurement matrices. "Unique solution" is stated as $\|X\|_*<\|Y\|_*$ for every feasible $Y\ne X$. The page quotes the result from Recht, Xu and Hassibi.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Theorem 6.3, p. 16

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Theorem 6.3** (Recht–Xu–Hassibi, Theorem 3). Let `S` be a linear map. Every `X` of rank at
most `k` is the unique solution of the nuclear norm minimization problem (6.3) for the datum
`𝓜 = S(X)` if and only if `S` satisfies the rank null space property of order `k`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Theorem 6.3, p. 16.

Formalization Notes: real matrices; `S` by measurement matrices. "Unique solution" is stated as
`‖X‖_* < ‖Y‖_*` for every feasible `Y ≠ X`. -/
theorem theorem_6_3 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    (∀ X : Matrix (Fin n) (Fin p) ℝ, X.rank ≤ k →
      ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = observationOp A X → Y ≠ X →
        nuclearNorm X < nuclearNorm Y) ↔ RNSP A k := by sorry

end IRLSM.Convergence
