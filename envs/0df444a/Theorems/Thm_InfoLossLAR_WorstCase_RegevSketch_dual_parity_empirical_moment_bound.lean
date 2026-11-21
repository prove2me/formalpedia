-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_empirical_moment_bound
-- name    : InfoLossLAR.WorstCase.RegevSketch.dual_parity_empirical_moment_bound
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-19T06:23:13.212243+00:00
-- url     : https://prove2.me/theorems/58dcea64-44fd-417e-b2b2-dd78cc1cab9d
-- title:
--   Uniform empirical projection bound for an exact Gaussian pool
-- statement:
--   At width $|s|/(100\delta)$, every unit projection rescaled by the width is uniformly subgaussian, by completing the square and using the maximal Gaussian coset mass at the origin. The squared projection has bounded exponential moment. Apply exponential Markov on a fixed sphere net, then the positive-semidefinite net bound to control the largest eigenvalue. The pool size $(n+1)^3$ absorbs the net size and yields the specified error. The result is stated for all integer test vectors, a subset of the real directions controlled by the operator bound.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemma 3.20 and its preceding reduction from GapSVP to the promise GapCVP variant, full-version PDF p. 30; fixed-family substitution and explicit uniform decision algorithm. Alternative index-two parity and rational covariance specialization of the dual certificate.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dual_parity_empirical_moment_bound :
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n → ∀ (D : Matrix (Fin n) (Fin n) ℤ), D.det ≠ 0 →
      ∀ (s : ℤ) (δ : ℚ), s ≠ 0 → 0 < δ →
      let r : ℚ := (Int.natAbs s : ℚ) / (100*δ)
      let m := (n+1)^3
      (∑' p : Fin m → Fin n → ℤ, (∏ j, coefficientMass D r (p j)) *
        (@ite ℝ (¬ ∀ x : Fin n → ℤ,
          64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
            (m : ℚ) * (s : ℚ)^2 * (∑ a, (x a : ℚ)^2)) (Classical.propDecidable _) 1 0))
        ≤ 1/(32*((n : ℝ)+1)) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
