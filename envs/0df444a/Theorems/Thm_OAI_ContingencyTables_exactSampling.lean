-- Prove2me | Theorems.Thm_OAI_ContingencyTables_exactSampling
-- name    : OAI.ContingencyTables.exactSampling
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:28.515862+00:00
-- url     : https://prove2.me/theorems/cc07b94d-873a-45ba-9ca5-a7e8b8694b39
-- statement:
--   The theorem states that there exist a single uniform randomized Post-Turing machine A (a finite transition table over an 8-symbol tape alphabet that consumes one random bit per step) and natural numbers C>0 and d such that, for every number of rows m, number of columns n, row sums r:Fin m→ℕ and column sums c:Fin n→ℕ with total row sum equal to total column sum, the following hold when A is run on the binary encoding of (m, n, r, c). Here a table is an m×n array of natural numbers with row sums r and column sums c, and Ω denotes the finite set of all such tables. First, whenever A halts on some finite prefix of random bits, its tape contains the row-major binary encoding of a genuine table with those margins. Second, for each table X, the probability that A has halted with output X after t random bits, namely the fraction of the 2^t bit strings doing so, converges as t→∞ to 1/|Ω|. Third, the probability that A has halted within t bits tends to 1. Fourth, the tail 1 − P(halted within t bits) is summable over t, and its sum, which is the expected number of random bits used, is at most C·(m + n + ⌈log₂(Σᵢ rᵢ + 1)⌉ + 1)^d, a polynomial bound uniform in all inputs. Thus this is a defined statement of exact uniform sampling of contingency tables with expected polynomial bit time; it is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContingencyTables.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContingencyTables.lean; bytes 9212..9344
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ContingencyTables

namespace OAI

namespace ContingencyTables

/-- Exact uniform sampling in polynomial expected bit time. -/
theorem exactSampling : Algorithms.ExactSamplingStatement := by sorry

end ContingencyTables
end OAI
