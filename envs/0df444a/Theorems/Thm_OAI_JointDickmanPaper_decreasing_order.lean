-- Prove2me | Theorems.Thm_OAI_JointDickmanPaper_decreasing_order
-- name    : OAI.JointDickmanPaper.decreasing_order
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:49.00222+00:00
-- url     : https://prove2.me/theorems/e319416a-7a43-4335-be47-b067bb2f9b49
-- statement:
--   The theorem states that the natural density of integers n for which the largest prime factor of n+1 is strictly smaller than the largest prime factor of n equals 1/2. Precisely, with maxPrimeFac(m) the last entry of the prime factorization list of m (with the conventions maxPrimeFac(0)=0 and maxPrimeFac(1)=1), and with realDensity(P)(X) defined as the number of integers n with 2 ≤ n ≤ ⌊X⌋ satisfying P(n), divided by the real number X, the claim is that realDensity of the predicate maxPrimeFac(n+1) < maxPrimeFac(n) tends to 1/2 as X tends to infinity. This is the reverse strict ordering counterpart of the stated corollary that maxPrimeFac(n) < maxPrimeFac(n+1) also has density 1/2. The result is admitted in the source rather than proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/JointDickman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/JointDickman.lean; bytes 1850..2060
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_JointDickman

namespace OAI

namespace JointDickmanPaper

open Filter JointDickman

open scoped Topology

/-- The reverse strict ordering also has natural density one half. -/
theorem decreasing_order :
    Tendsto (realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac))
      atTop (𝓝 (1 / 2)) := by
  sorry

end JointDickmanPaper
end OAI
