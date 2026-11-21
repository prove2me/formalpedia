-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_odd_count_bound
-- name    : InfoLossLAR.WorstCase.RegevSketch.dual_parity_odd_count_bound
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-19T06:23:20.680898+00:00
-- url     : https://prove2.me/theorems/d8fb39e8-0e21-48d6-b528-9533a1d8be00
-- title:
--   Odd coefficient count for an ideal above-smoothing Gaussian pool
-- statement:
--   At twice the smoothing parameter, the discrete Gaussian reduced modulo two is close to uniform. Thus an individual coefficient is odd with probability at least $3/8$ when the smoothing error is at most $1/8$ (using the pointwise coset bounds). For $(n+1)^3$ independent draws, a binomial deviation bound makes the probability of fewer than a quarter of the draws being odd at most $1/(32(n+1))$ eventually. The full countable product distribution has total mass one.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemma 3.20 and its preceding reduction from GapSVP to the promise GapCVP variant, full-version PDF p. 30; fixed-family substitution and explicit uniform decision algorithm. Alternative index-two parity and rational covariance specialization of the dual certificate.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dual_parity_odd_count_bound :
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n → ∀ (D : Matrix (Fin n) (Fin n) ℤ), D.det ≠ 0 →
      ∀ r : ℝ, 0 < r → smoothingError n ≤ 1/8 →
      RegevLWE.GaussConv.smoothingParam (inputModule D) (smoothingError n) ≤ r/2 →
      let m := (n+1)^3
      HasSum (fun p : Fin m → Fin n → ℤ => ∏ j, coefficientMass D r (p j)) 1 ∧
      ∀ i : Fin n,
        (∑' p : Fin m → Fin n → ℤ, (∏ j, coefficientMass D r (p j)) *
          (@ite ℝ (¬ (m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card))
            (Classical.propDecidable _) 1 0)) ≤ 1/(32*((n : ℝ)+1)) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
