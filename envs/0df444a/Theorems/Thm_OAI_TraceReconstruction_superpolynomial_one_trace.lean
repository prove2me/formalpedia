-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_superpolynomial_one_trace
-- name    : OAI.TraceReconstruction.superpolynomial_one_trace
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:33.938185+00:00
-- url     : https://prove2.me/theorems/8d0ddc00-c5be-437b-829b-53ad79f825fb
-- statement:
--   The theorem states that, for every deletion probability q strictly between 0 and 1 and every real exponent C>0, the quantity n^C · minTraceTV(n,q) tends to 0 as n tends to infinity through the natural numbers. Here, for a binary word x of length n, a trace is obtained by an independent mask that deletes each bit with probability q and retains it with probability 1−q, the observer seeing only the resulting list of retained bits. traceTV(q,x,y) is the total variation distance, one half the sum of absolute differences of probabilities, between the trace distributions of two words x and y over the finite space of all Boolean lists of length at most n. minTraceTV(n,q) is the infimum of traceTV(q,x,y) over all pairs of distinct words x≠y of length n. Thus the closest pair of distinct words has single-trace distance that decays faster than every polynomial in 1/n. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TraceReconstruction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TraceReconstruction.lean; bytes 2951..3137
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

theorem superpolynomial_one_trace
    (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ C * minTraceTV n q) atTop (𝓝 0) := by
  sorry

end TraceReconstruction
end
end OAI
