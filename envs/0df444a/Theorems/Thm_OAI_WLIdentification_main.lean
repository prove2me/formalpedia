-- Prove2me | Theorems.Thm_OAI_WLIdentification_main
-- name    : OAI.WLIdentification.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.003802+00:00
-- url     : https://prove2.me/theorems/061c54c3-253a-4a3b-afe5-8503fae2c04e
-- statement:
--   The theorem states that dimensionLanguage is EXPTIME-complete, a claim whose proof is admitted rather than supplied. The language consists of binary words encoding a pair (G,k): a unary header of G.order ones followed by a zero, then the row-major adjacency matrix of a simple undirected graph G on a positive number of vertices, then the binary digits of a positive integer k written most significant bit first with a leading 1, such that the Weisfeiler-Leman dimension of G, defined as the least positive k' for which k'-dimensional Weisfeiler-Leman equivalence (neighbor-color refinement for k'=1, joint tuple refinement otherwise, over all rounds) forces isomorphism with every graph, is at most k. Malformed words are rejected. EXPTIME-completeness means two things for a language S of bit words. First, S is decided by a deterministic single-tape Turing machine, with finite tables of extra symbols and states, that halts on every input word, accepting exactly the members, within time 2^(C(n+1)^d) for some constants C and d, where n is the input length. Second, every language decidable in that exponential time reduces to S by a many-one reduction computed by such a machine in polynomial time C(n+1)^d, writing its output word on the tape.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WLIdentification.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WLIdentification.lean; bytes 5536..5602
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_WLIdentification

namespace OAI

namespace WLIdentification

theorem main : EXPTIMEComplete dimensionLanguage :=
  by
    sorry

end WLIdentification
end OAI
