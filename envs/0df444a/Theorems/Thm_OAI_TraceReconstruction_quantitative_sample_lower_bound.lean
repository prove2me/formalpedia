-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_quantitative_sample_lower_bound
-- name    : OAI.TraceReconstruction.quantitative_sample_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:33.799293+00:00
-- url     : https://prove2.me/theorems/36f87ae3-b30a-4b87-a7af-25350d9321dd
-- statement:
--   The theorem states that, for fixed s in (0,1] and fixed c with 0 < c < 1/(4 ln 2), the following holds for every sequence of word lengths n_k tending to infinity and every sequence of deletion probabilities q_k in the open interval (0,1) such that q_k³ ln(n_k) tends to infinity: for all sufficiently large k, n_k raised to the real power c·ln(q_k³ ln n_k), viewed as an extended nonnegative real, is at most the sample complexity of reconstructing words of length n_k at deletion probability q_k with success level s. Here a trace of a binary word x of length n is obtained by an independent deletion mask that retains each bit with probability 1−q and deletes it with probability q, and the observer sees only the resulting list of retained bits, with no positions revealed. With m independent traces, an estimator is a map from the m-tuple of traces to a probability distribution over words of length n. A budget m is sufficient if some estimator has, for every word x, probability at least s of outputting exactly x, averaged over the m independent masks. The sample complexity is the infimum of the sufficient budgets m, taken in the extended nonnegative reals, and equals infinity if no budget suffices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TraceReconstruction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TraceReconstruction.lean; bytes 2472..2949
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TraceReconstruction

namespace OAI

open scoped ENNReal

noncomputable section

namespace TraceReconstruction

open Filter

open scoped Topology Classical ENNReal

theorem quantitative_sample_lower_bound
    (s c : ℝ) (hs : s ∈ Set.Ioc 0 1)
    (hc : c ∈ Set.Ioo 0 (1 / (4 * Real.log 2)))
    (n : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hq : ∀ k, q k ∈ Set.Ioo 0 1)
    (hscale : Tendsto (fun k => (q k) ^ 3 * Real.log (n k)) atTop atTop) :
    ∀ᶠ k in atTop,
      ENNReal.ofReal ((n k : ℝ) ^ (c * Real.log ((q k) ^ 3 * Real.log (n k)))) ≤
        sampleComplexity (n k) (q k) s := by
  sorry

end TraceReconstruction
end
end OAI
