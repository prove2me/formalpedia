-- Prove2me | Theorems.Thm_OAI_Dixmier_current_main_theorem
-- name    : OAI.Dixmier.current_main_theorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:35.943568+00:00
-- url     : https://prove2.me/theorems/7cebdde2-81d2-4a40-a81b-016946285e8c
-- statement:
--   The theorem states that for every discrete group G (a group with the discrete topology), G is amenable if and only if it is unitarizable, and moreover non-amenable groups have uniformly nearly bounded non-unitarizable representations. Here amenable means there is a ℂ-linear functional m on the bounded complex-valued functions on G with m(1)=1, which sends every function taking nonnegative real values to a nonnegative real number, and which is invariant under left translation, where the translate of f by g is x ↦ f(g⁻¹x). A representation π of G by bounded linear operators on a complex inner product space H is similar to unitary if there is a bounded linear bijection S of H with bounded inverse such that ‖S π(g) S⁻¹ x‖ = ‖x‖ for all g and x. G is unitarizable if every group homomorphism π from G into the bounded operators of any complete complex inner product space (a Hilbert space) H in the universe max(u,v), where u is the universe of G, that is uniformly bounded, meaning ‖π(g)‖ ≤ C for some constant C and all g, is similar to unitary. The second conclusion says that for every ε>0 and every non-amenable G, there exist a Hilbert space H and a representation π of G on H with ‖π(g)‖ ≤ 1+ε for all g that is not similar to unitary; and if G is countable, H can be taken separable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DixmierAllDiscrete.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DixmierAllDiscrete.lean; bytes 1795..1864
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Definitions.Def_DixmierAllDiscrete

namespace OAI

noncomputable section

universe u v

namespace Dixmier

open scoped BoundedContinuousFunction

theorem current_main_theorem : CurrentMainTheorem.{u,v} := by
  sorry

end Dixmier
end
end OAI
