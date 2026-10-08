-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_eq_2_1
-- name    : MinRankRecovery.Recovery.eq_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:46.844261+00:00
-- url     : https://prove2.me/theorems/8bfe0ef4-3fd4-4dee-941b-5d6f10a8ce9d
-- title:
--   (2.1) — ‖X‖ ≤ ‖X‖_F ≤ ‖X‖_* ≤ √r ‖X‖_F ≤ r ‖X‖ for rank X ≤ r
-- statement:
--   For a real $m\times n$ matrix $X$ with singular values $\sigma_1(X)\ge\sigma_2(X)\ge\dots\ge0$, write $\|X\|=\sigma_1(X)$ for the operator norm, $\|X\|_F=(\sum_i\sigma_i(X)^2)^{1/2}$ for the Frobenius norm, and $\|X\|_*=\sum_i\sigma_i(X)$ for the nuclear norm. If $X$ has rank at most $r$, then
--   $$\|X\|\;\le\;\|X\|_F\;\le\;\|X\|_*\;\le\;\sqrt r\,\|X\|_F\;\le\;r\,\|X\|.$$
--
--   These comparisons between the three unitarily invariant norms are used throughout the paper; in the proof of Theorem 3.3 they convert a nuclear-norm bound on a matrix of rank at most $2r$ into a Frobenius-norm bound.
--
--   **Formalization Note** The norms are `opNorm` (supremum of $\|Xv\|_2$ over unit vectors $v$), `frobeniusNorm` and `nuclearNorm` (sum of the singular values) from the referenced module `HighDimStat_MatrixRank_Core`. All four inequalities are stated, for every natural number $r$; at $r=0$ the matrix is zero and every term vanishes.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, §2 'Matrix vs. Vector Norms', (2.1), p. 6

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- (2.1), p. 6: for every matrix `X` of rank at most `r`,
`‖X‖ ≤ ‖X‖_F ≤ ‖X‖_* ≤ √r ‖X‖_F ≤ r ‖X‖`. -/
theorem eq_2_1 {m n : ℕ} (r : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) (hX : X.rank ≤ r) :
    opNorm X ≤ frobeniusNorm X ∧ frobeniusNorm X ≤ nuclearNorm X ∧
      nuclearNorm X ≤ Real.sqrt r * frobeniusNorm X ∧
      Real.sqrt r * frobeniusNorm X ≤ r * opNorm X := by sorry

end MinRankRecovery.Recovery
