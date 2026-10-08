-- Prove2me | Theorems.Thm_OAI_ThompsonNonamenability_thompson_F_nonamenable_composition
-- name    : OAI.ThompsonNonamenability.thompson_F_nonamenable_composition
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.77584+00:00
-- url     : https://prove2.me/theorems/884d1e77-0487-41bb-83a5-3ccc22e72403
-- statement:
--   The theorem states that, on the type F of Thompson-group candidates, there exists a group structure whose multiplication is composition of maps and which has no invariant mean. Here F consists of homeomorphisms f of the unit interval [0,1] that are strictly increasing and have dyadic piecewise-linear pieces: there is a finite partition of [0,1] by strictly increasing knots, starting at 0 and ending at 1, all of them dyadic rationals k/2^n, such that on each piece f is affine with slope 2^e for some integer e. The group structure is required to satisfy (h*g)(x) = h(g(x)) for all h, g in F and all x in [0,1]. An invariant mean on a group G is a real-linear functional on the space of bounded real-valued functions on G (the sup-norm space ℓ^∞(G)) that is nonnegative on every pointwise nonnegative function, sends the constant function 1 to 1, and is left invariant, meaning its value on the function g ↦ f(h*g) equals its value on f for every h in G and bounded f. The conclusion is that no such invariant mean exists for F, so F with this composition group structure is nonamenable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThompsonNonamenability.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThompsonNonamenability.lean; bytes 2424..2683
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_ThompsonNonamenability

namespace OAI

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G]

theorem thompson_F_nonamenable_composition :
    ∃ group : Group F, letI := group;
      (∀ (h g : F) (x : UnitInterval),
        (h * g).val.toHomeomorph x = h.val.toHomeomorph (g.val.toHomeomorph x)) ∧
      ¬ Nonempty (InvariantMean F) := by
  sorry

end ThompsonNonamenability
end
end OAI
