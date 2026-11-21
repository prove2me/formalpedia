-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_search_to_single_coefficient_gaussian
-- name    : InfoLossLAR.WorstCase.RegevSearch.search_to_single_coefficient_gaussian
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T13:41:01.672997+00:00
-- url     : https://prove2.me/theorems/8c7e18f0-5ede-48c1-862d-8bbb16d6033d
-- title:
--   One lattice Gaussian coefficient vector from fixed-family LWE search
-- statement:
--   Let $S$ be an infinite set of positive dimensions. At each sufficiently large $n\in S$, suppose one uniform quantum polynomial-time algorithm recovers each fixed secret with probability at least $3/4$ from a fresh table of the specified fixed-family discrete Gaussian LWE distribution. One polynomial bounds the number of table blocks.
--
--   There is a uniform quantum polynomial-time sampler $H$ and a negligible function $\varepsilon$. For every sufficiently large $n\in S$, every nonsingular integer basis $B$, every positive rational width $r$ at least the platform DGS threshold, and every unary precision parameter $k$, the measured output of $H$ starts with a valid encoding of a single vector of integer coefficients. If $p(z)$ is the probability of the prefix encoding $z$ and $D_{B,r}(z)$ is the normalized Gaussian coefficient mass for the original basis, then
--
--   $$
--   \sum_z p(z)=1,\qquad \sum_z |p(z)-D_{B,r}(z)|\leq \varepsilon(n)+\frac{1}{k+1}.
--   $$
--
--   The sampler uses the DGS input format with count one and emits the inner coefficient-vector encoding. The same family and intrinsic error apply to every basis, width and precision in a given dimension. This is the one-sample search-to-DGS construction needed before independent repetitions can supply a whole pool.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.2–3.4 and 3.14, pp. 18–20, 26–28. Regev's theorem outputs one lattice Gaussian sample. The discrete fixed-family noise conversion, the uniform Clifford+T implementation, coefficient encoding, L1 constant and tunable precision here are explicit additional obligations of the platform formulation.

import Definitions.Def_InfoLossLAR_RegevSearch

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem search_to_single_coefficient_gaussian
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (A : MFamily) (hA : IsMQPT A) (samples : Polynomial ℕ) (cutoff : ℕ)
    (hsearch : SearchOn A samples cutoff S) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ error : ℕ → ℝ, Negligible error ∧
      ∃ threshold : ℕ, ∀ n ∈ S, threshold ≤ n →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∀ precision : ℕ,
          let draw (z : Fin n → ℤ) := outputProb H (dgsInput B r 1 precision)
            (fun out => encVec encI z <+: out)
          HasSum draw 1 ∧
            (∑' z, |draw z - coefficientMass B r z|) ≤
              error n + 1 / ((precision : ℝ) + 1) := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
