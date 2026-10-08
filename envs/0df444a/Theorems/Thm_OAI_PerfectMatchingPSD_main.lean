-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_main
-- name    : OAI.PerfectMatchingPSD.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:02.356707+00:00
-- url     : https://prove2.me/theorems/0143f599-f493-4f04-9ce9-c03e7960a1fa
-- statement:
--   The theorem states that the defined proposition MainClaim holds. Edges on vertex set {0,…,n−1} are pairs (a,b) with a<b, and a perfect matching is a set of edges such that every vertex lies in exactly one chosen edge. The rows are indexed by all edges together with all odd-cardinality vertex subsets U. For a perfect matching M, the slack of an edge row e is 1 if e∈M and 0 otherwise, while the slack of an odd-set row U is the number of edges of M crossing U (exactly one endpoint in U) minus 1. HasFactorization(n,r) says there exist real symmetric positive semidefinite r×r matrices A_i for every row i and B_M for every perfect matching M, with no equivariance or rank-one restriction, such that slack(i,M)=trace(A_i B_M) for all rows i and matchings M. psdRank(n) is the least positive r admitting such a factorization, taken as an infimum over naturals, so it is 0 if none exists. MainClaim asserts that for every real C>0 there is n₀≥4 such that for all even n≥n₀, n^C<psdRank(n), where n^C is real exponentiation; thus the PSD rank of this slack matrix exceeds every fixed polynomial in n eventually.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingPSD.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingPSD.lean; bytes 1759..1797
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MatchingPSD

namespace OAI

namespace PerfectMatchingPSD

theorem main : MainClaim := by
  sorry

end PerfectMatchingPSD
end OAI
