-- Prove2me | Theorems.Thm_OAI_Dixmier_main_theorem_all_universes
-- name    : OAI.Dixmier.main_theorem_all_universes
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:36.100612+00:00
-- url     : https://prove2.me/theorems/d6a263ae-62d1-439f-9809-06849a44bcc9
-- statement:
--   The theorem states that, for every group G that is countable and carries the discrete topology, if G is not amenable then G has a bounded nonunitarizable witness, with the universe of G and the universe of the Hilbert space chosen independently. Here G is amenable if there is a complex-linear functional m on bounded complex-valued functions on G with m(1)=1, which is positive in the sense that m(f) is a nonnegative real whenever every value f(x) is a nonnegative real, and which is invariant under left translation, meaning m of the function x ↦ f(g⁻¹x) equals m(f) for every g in G. A witness is a complete, separable complex Hilbert space H together with a group homomorphism π from G into the bounded linear operators on H such that ‖π(g)‖ ≤ 101 for every g, and π is not similar to a unitary representation. Similar to unitary means there is no bounded invertible linear operator S on H, with bounded inverse, such that ‖S π(g) S⁻¹ x‖ = ‖x‖ for all g in G and x in H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Dixmier.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Dixmier.lean; bytes 1813..1957
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Definitions.Def_Dixmier

namespace OAI

noncomputable section

universe u v

namespace Dixmier

open scoped BoundedContinuousFunction

/-- The main theorem with independent group and Hilbert-space universes. -/
theorem main_theorem_all_universes : MainTheorem.{u,v} := by
  sorry

end Dixmier
end
end OAI
