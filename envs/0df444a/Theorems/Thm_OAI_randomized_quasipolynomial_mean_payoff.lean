-- Prove2me | Theorems.Thm_OAI_randomized_quasipolynomial_mean_payoff
-- name    : OAI.randomized_quasipolynomial_mean_payoff
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:41.281102+00:00
-- url     : https://prove2.me/theorems/2b67bfe8-cb0e-4468-9bf2-5fdbaaeec661
-- statement:
--   The theorem states that the defined proposition MeanPayoff.MainClaim holds, which asserts a randomized quasipolynomial-time algorithm for deciding winning vertices in mean-payoff games. A game is a finite directed graph with n>0 vertices and m edges, each edge having a tail, a head and an integer weight, each vertex owned by the maximizer or the minimizer, and every vertex having at least one outgoing edge. A strategy chooses, from the history of edges played and the current vertex, an outgoing edge of that vertex. Given strategies σ and τ and a start vertex, play follows σ at maximizer vertices and τ at the others, producing an infinite edge sequence whose payoff is the liminf of the average weight over the first T edges. A vertex is winning if some σ guarantees payoff at least 0 against every τ. A game is encoded as a bit string: self-delimiting binary codes of n and m, the owner bits, then for each edge its tail+1, head+1 and a signed weight. The machine model is a randomized Turing machine with three tapes over Option Bool, where tape 0 holds the input, tape 2 is the output, and each step reads the current symbols plus one random bit and either halts or writes, shifts each head left, right or not at all, and changes state. MainClaim says there exist a machine M and a real C>0 such that for every game G there is a running time T with T ≤ 2^(C·(log₂(|input(G)|+2))²), where |input(G)| is the encoding length, and the following hold when M runs on input(G) for exactly T steps using T random bits (extra bits being false): the machine has halted for every possible random string, and for at least 7/8 of all 2^T random strings the output tape is correct, meaning it holds true at position v exactly for the winning vertices, false at position v exactly for the non-winning vertices, for v from 0 to n-1, and is blank elsewhere.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RandomizedMeanPayoff.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RandomizedMeanPayoff.lean; bytes 4011..4094
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_RandomizedMeanPayoff

namespace OAI

theorem randomized_quasipolynomial_mean_payoff : MeanPayoff.MainClaim := by
  sorry

end OAI
