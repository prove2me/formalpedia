-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_pool_gaussian_tail
-- name    : InfoLossLAR.WorstCase.RegevSketch.dgs_pool_gaussian_tail
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:01:51.341771+00:00
-- url     : https://prove2.me/theorems/3c890e2f-9685-49f4-8f30-6aee45440ab1
-- title:
--   Normalization and radial tail of the ideal DGS pool
-- statement:
--   Transport the Gaussian through the coefficient bijection for the nonsingular integer basis. The normalized one-point mass is summable with total one; finite independence gives product normalization and the same marginal at each slot. The Gaussian radial tail bounds each failure by $4^{-n}$; take the union bound over $16(n+1)^2$ slots.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemmas 3.15–3.17, full-version PDF pp. 28–29; fixed-family substitution and explicit uniform multi-output realization.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dgs_pool_gaussian_tail : ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
  ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 →
  ∀ r : ℝ, 0 < r → dgsThreshold B ≤ r →
    HasSum (fun pool : Fin (16 * (n + 1)^2) → Fin n → ℤ => (∏ i, coefficientMass B r (pool i))) 1 ∧
    (∑' pool : Fin (16 * (n + 1)^2) → Fin n → ℤ,
      (∏ i, coefficientMass B r (pool i)) * (if ∃ i, 2 * Real.sqrt n * r < ‖latVec B (pool i)‖ then 1 else 0))
        ≤ (16 * ((n : ℝ) + 1)^2) * (1/4 : ℝ)^n := by sorry

end InfoLossLAR.WorstCase.RegevSketch
