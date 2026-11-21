-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_ideal_short_spanning_pool
-- name    : InfoLossLAR.WorstCase.RegevSketch.dgs_ideal_short_spanning_pool
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T22:50:55.340672+00:00
-- url     : https://prove2.me/theorems/d7fb7f0f-5bc7-4309-9ca6-08a48a84c6f3
-- title:
--   Short independent vectors in an ideal DGS pool
-- statement:
--   In all sufficiently large positive dimensions, a pool of $16(n+1)^2$ independent exact discrete Gaussian samples at any admissible width contains $n$ independent vectors of norm at most twice that width times $\sqrt n$ with probability at least $7/8$. Interpret samples as original-basis coefficients. Use Regev’s constant escape probability from any proper span, followed by Gaussian norm concentration and a union bound over the pool.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemmas 3.15–3.17, full-version PDF pp. 28–29; fixed-family substitution and explicit uniform multi-output realization.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dgs_ideal_short_spanning_pool :    ∃ n₀ : ℕ, ∀ n ≥ n₀, 1 ≤ n →
      ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 →
      ∀ r : ℝ, 0 < r → dgsThreshold B ≤ r →
        (7 : ℝ)/8 ≤ ∑' pool : Fin (16 * (n + 1)^2) → Fin n → ℤ,
          (∏ i, coefficientMass B r (pool i)) *
          (if ∃ pick : Fin n → Fin (16 * (n + 1)^2),
            LinearIndependent ℝ (fun i => latVec B (pool (pick i))) ∧
              ∀ i, ‖latVec B (pool (pick i))‖ ≤ 2 * Real.sqrt n * r
           then 1 else 0) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
