-- Prove2me | Theorems.Thm_IRLSM_Convergence_corollary_6_7
-- name    : IRLSM.Convergence.corollary_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:58.298976+00:00
-- url     : https://prove2.me/theorems/43a20095-1730-4ac6-930f-f4ab5d4a5d1d
-- title:
--   Corollary 6.7 — SRNSP gives $\|X-\bar X\|_*\le2\frac{1+\eta}{1-\eta}\rho_k(X)_*$, exact $k$-rank recovery, and the RNSP
-- statement:
--   Suppose $\mathcal S$ satisfies the strong rank null space property of order $k$ with constant $\eta\in(0,1)$. Let $X$ be any matrix and $\mathscr M=\mathcal S(X)$. Then every solution $\bar X$ of the nuclear norm minimization problem $\min\|Y\|_*$ subject to $\mathcal S(Y)=\mathscr M$ satisfies
--   $$\|X-\bar X\|_*\le2\,\frac{1+\eta}{1-\eta}\,\rho_k(X)_* .$$
--   In particular, every $X$ of rank at most $k$ is the unique solution of this problem, and $\mathcal S$ satisfies the rank null space property of order $k$.
--
--   The strong null space property thus yields stable low-rank recovery by nuclear norm minimization.
--
--   **Formalization Note** Real matrices; $\mathcal S$ is given by measurement matrices. A solution $\bar X$ is a feasible matrix with $\|\bar X\|_*\le\|Y\|_*$ for every feasible $Y$; "unique solution" is stated as $\|X\|_*<\|Y\|_*$ for every feasible $Y\ne X$.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Corollary 6.7, p. 18; (6.3), p. 16

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Corollary 6.7.** Suppose `S` satisfies the SRNSP of order `k` with constant `η ∈ (0, 1)`.
For every `X` and every solution `X̄` of the nuclear norm minimization problem (6.3) with datum
`𝓜 = S(X)`, `‖X − X̄‖_* ≤ 2 (1 + η)/(1 − η) ρ_k(X)_*`. In particular every `X` of rank at most `k`
is the unique solution of (6.3) for `𝓜 = S(X)`, and `S` has the rank null space property of
order `k`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Corollary 6.7, p. 18; (6.3), p. 16.

Formalization Notes: real matrices; `S` by measurement matrices. A solution of (6.3) is a feasible
`X̄` with `‖X̄‖_* ≤ ‖Y‖_*` for every feasible `Y`; "unique solution" is stated as the strict
inequality `‖X‖_* < ‖Y‖_*` for every feasible `Y ≠ X`. -/
theorem corollary_6_7 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (η : ℝ)
    (hS : SRNSP A k η) :
    (∀ X Xbar : Matrix (Fin n) (Fin p) ℝ, observationOp A Xbar = observationOp A X →
      (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = observationOp A X →
        nuclearNorm Xbar ≤ nuclearNorm Y) →
      nuclearNorm (X - Xbar) ≤ 2 * (1 + η) / (1 - η) * rho k X) ∧
    (∀ X : Matrix (Fin n) (Fin p) ℝ, X.rank ≤ k →
      ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = observationOp A X → Y ≠ X →
        nuclearNorm X < nuclearNorm Y) ∧
    RNSP A k := by sorry

end IRLSM.Convergence
