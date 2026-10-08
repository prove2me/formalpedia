-- Prove2me | Theorems.Thm_OAI_VariableWL_main
-- name    : OAI.VariableWL.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:37.404584+00:00
-- url     : https://prove2.me/theorems/c3edea93-3cde-4046-a1e9-4390dad99d2d
-- statement:
--   The theorem states that two languages of binary words are EXPTIME-complete: WL and SubWL. EXPTIME-complete means that a language L is decided by a multi-tape Turing machine, with any finite number of states, work symbols and extra tapes, in time at most 2^(c(n+1)^d) on inputs of length n for some constants c and d, and that every such exponential-time language R reduces to L by a machine computing a map w to out in time at most c(n+1)^d, with w in R if and only if out in L. Inputs and outputs are read from and written to the first tape as bit strings, and a computation must halt with that tape holding exactly the output word. WL consists of the codes of triples (G,H,k) of finite simple graphs G and H and an integer k with k at least 2 such that G and H are k-dimensional Weisfeiler-Leman equivalent as defined here. The colour of a k-tuple of vertices starts as its equality and adjacency pattern, and each refinement round pairs the previous colour with the multiset, over all vertices z, of the colours obtained by replacing each coordinate in turn by z. G and H are equivalent when, for every number of rounds, the multisets of colours of all k-tuples agree. A triple is coded by concatenating the adjacency-matrix codes of G and H and a code of k, where each integer is written as a unary length, a zero, then its binary digits. SubWL is the restriction of WL to triples with k at least 2 where G and H have the same positive number of vertices, are both connected, and have maximum degree at most 3.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/VariableWL.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VariableWL.lean; bytes 4008..4081
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_VariableWL

namespace OAI

namespace VariableWL

theorem main : EXPTIMEComplete WL ∧ EXPTIMEComplete SubWL := by
  sorry

end VariableWL
end OAI
