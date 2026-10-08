-- Prove2me | Theorems.Thm_OAI_JointDickmanPaper_increasing_order
-- name    : OAI.JointDickmanPaper.increasing_order
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:49.165557+00:00
-- url     : https://prove2.me/theorems/0a084f4a-a7d3-44e0-bcca-15b9fbf2dec1
-- statement:
--   The theorem states that the proportion of integers n for which the largest prime factor of n is strictly smaller than the largest prime factor of n+1 tends to 1/2. Here maxPrimeFac(n) is the largest prime factor of n (with the Mathlib defaults maxPrimeFac 0 = 0 and maxPrimeFac 1 = 1), and the proportion is realDensity: for a real endpoint X, the number of integers n with 2 ≤ n ≤ ⌊X⌋ satisfying the condition, divided by X. Formally, as X tends to infinity along the reals, realDensity of the predicate maxPrimeFac(n) < maxPrimeFac(n+1) converges to 1/2. This is the source's Corollary 2 about the increasing strict ordering of consecutive largest prime factors, stated as an admitted theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/JointDickman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/JointDickman.lean; bytes 1627..1848
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_JointDickman

namespace OAI

namespace JointDickmanPaper

open Filter JointDickman

open scoped Topology

/-- Corollary 2: the increasing strict ordering has natural density one half. -/
theorem increasing_order :
    Tendsto (realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac))
      atTop (𝓝 (1 / 2)) := by
  sorry

end JointDickmanPaper
end OAI
