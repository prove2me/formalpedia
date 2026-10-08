-- Prove2me | Theorems.Thm_OAI_LoopMatching_fullEndpoint
-- name    : OAI.LoopMatching.fullEndpoint
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:54.377306+00:00
-- url     : https://prove2.me/theorems/0d49ff1c-c859-49b9-8078-3af4fd98a347
-- statement:
--   The theorem states that a finite-alphabet polynomial-time rational approximation scheme exists for weighted singleton-loop matchings. An input consists of an ordinary multigraph on n vertices, given as a duplicate-free list of records (i,j,multiplicity) with i<j<n, together with a duplicate-free list of loop records (v,multiplicity) with v<n; absent pairs and vertices have multiplicity 0. A partial matching is a set of pairs i<j in which no vertex lies in two distinct chosen pairs. Its weight is the product of the pair multiplicities over the chosen pairs, times the product of the loop multiplicities over all vertices not covered by any chosen pair. The count of the input is the sum of these weights over all partial matchings. Inputs are encoded as binary strings with self-delimiting unary-length encodings of naturals, and outputs are pairs of naturals (a,b) encoded the same way. The claim is that there is a function A from inputs to such pairs, computed by a polynomial-time multi-tape Turing machine whose tape alphabets are all finite, with output length bounded by a polynomial in the input length, such that for every input G with A(G)=(a,b): b>0, a ≤ b·count(G), b·count(G) ≤ 2^(18n)·a, and a=0 exactly when count(G)=0. So a/b approximates the count within a factor of 2^(18n), where n is the number of vertices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SingletonLoopMatching.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SingletonLoopMatching.lean; bytes 3886..4029
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SingletonLoopMatching

namespace OAI

universe u_1 u_2

open scoped BigOperators

namespace LoopMatching

/-- A finite-alphabet polynomial-time rational approximation for singleton-loop matchings. -/
theorem fullEndpoint : FullEndpoint := by
  sorry

end LoopMatching
end OAI
