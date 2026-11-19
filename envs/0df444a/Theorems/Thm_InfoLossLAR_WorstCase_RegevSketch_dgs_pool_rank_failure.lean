-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_pool_rank_failure
-- name    : InfoLossLAR.WorstCase.RegevSketch.dgs_pool_rank_failure
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:01:53.377437+00:00
-- url     : https://prove2.me/theorems/df0bd4b7-038d-4a90-8b4f-1612ace2c24d
-- title:
--   Rank failure of the ideal DGS pool
-- statement:
--   At sufficiently large dimension the fixed-family width also smooths the doubled lattice. The coefficient residue law modulo two is within total variation $1/15$ of uniform, so each binary hyperplane has one-sample mass at most $3/5$. Full binary rank implies real independence by the odd determinant of a selected minor and nonsingularity of the original basis. A union bound over nonzero binary linear functionals gives failure at most $2^n(3/5)^{16(n+1)^2}\le 2^{-n}$, by using at least $4n$ samples.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemmas 3.15–3.17, full-version PDF pp. 28–29; fixed-family substitution and explicit uniform multi-output realization.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dgs_pool_rank_failure : ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
  ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 →
  ∀ r : ℝ, 0 < r → dgsThreshold B ≤ r →
    (∑' pool : Fin (16 * (n + 1)^2) → Fin n → ℤ,
      (∏ i, coefficientMass B r (pool i)) * (if ¬ ∃ pick : Fin n → Fin (16 * (n + 1)^2),
        LinearIndependent ℝ (fun i => latVec B (pool (pick i))) then 1 else 0))
        ≤ (1/2 : ℝ)^n := by sorry

end InfoLossLAR.WorstCase.RegevSketch
