-- Prove2me | Theorems.Thm_OAI_CubeShuffle_WeightedSweep_weighted_sweep_moments
-- name    : OAI.CubeShuffle.WeightedSweep.weighted_sweep_moments
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:31.364862+00:00
-- url     : https://prove2.me/theorems/190fc0cb-c344-417a-885e-a38d4ea29f86
-- statement:
--   The theorem states that there exist a function W assigning a strictly positive real weight to every Young diagram, a real constant pStar ≥ 2, and exponents p(d) for each d ≥ 1 with 2 ≤ p(d) ≤ pStar, such that the following holds for every d ≥ 1 and every Young diagram μ with exactly 2^d cells. Let dim(μ) be the complex dimension of the Specht module of μ, spanned by the translates of the polytabloid in the permutation space on tabloids of μ, regarded as a Hilbert subspace. Let the Fourier sweep be the average, over all sequences ω of d coin configurations, of the unitary operator by which the product of d card-shuffling steps run(d,d)(ω) acts on this space; each step composes a cyclic rotation of the d-bit positions with a pair switch that flips the first bit according to a coin function of the remaining bits, and the 2^d card positions are identified with the cells of μ by a fixed bijection. Then dim(μ)^(3/4) ≤ W(μ) ≤ dim(μ); W(μ) times the p(d)-th power of the Schatten p(d)-norm of the Fourier sweep (the p(d)-th root of the sum of the p(d)-th powers of its singular values) is at most 1; and the operator norm of the Fourier sweep is at most dim(μ)^(-3/(4·pStar)). The proof is admitted in the source rather than established.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeightedSweepMoments.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeightedSweepMoments.lean; bytes 10593..11167
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_WeightedSweepMoments

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep

open Specht UnitaryFinite

theorem weighted_sweep_moments :
    ∃ (W : YoungDiagram → ℝ) (pStar : ℝ) (p : ℕ → ℝ),
      (∀ μ : YoungDiagram, 0 < W μ) ∧
      2 ≤ pStar ∧
      (∀ d : ℕ, 1 ≤ d → 2 ≤ p d ∧ p d ≤ pStar) ∧
      ∀ d : ℕ, 1 ≤ d → ∀ μ : Shapes (2 ^ d),
        dimension μ.1 ^ (3 / 4 : ℝ) ≤ W μ.1 ∧
        W μ.1 ≤ dimension μ.1 ∧
        W μ.1 *
          schattenNorm (V := hilbertSpace μ.1) (fourierSweep d μ) (p d) ^ (p d) ≤ 1 ∧
        ‖fourierSweep d μ‖ ≤ dimension μ.1 ^ (-3 / (4 * pStar)) := by
  sorry

end CubeShuffle.WeightedSweep
end
end OAI
