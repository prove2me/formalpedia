-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_exists_fixedPoint_of_canonicallyReflexive
-- name    : OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:15.175984+00:00
-- url     : https://prove2.me/theorems/378c1973-ae37-44ee-bb2e-b5c60a0a74e9
-- statement:
--   The theorem states that, for a real normed space X that is complete (a Banach space) and canonically reflexive, meaning the canonical embedding of X into its continuous bidual is surjective, every nonexpansive selfmap of a nonempty closed bounded convex subset C of X has a fixed point. Precisely, given C nonempty, closed, bounded and convex over ℝ, and a map F from C to C satisfying ‖F(a) − F(b)‖ ≤ ‖a − b‖ for all a and b in C, with the norm being the original norm of X, there exists a point a in C with F(a) = a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ReflexiveFixedPoints.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ReflexiveFixedPoints.lean; bytes 347..919
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ReflexiveFixedPoints

namespace OAI

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {X}

/-- Every nonexpansive selfmap of a nonempty closed bounded convex set has
an actual fixed point, with nonexpansiveness stated in the original norm. -/
theorem exists_fixedPoint_of_canonicallyReflexive
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : CanonicallyReflexive X) (C : Set X)
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C)
    (hF : ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖) :
    ∃ a : C, F a = a := by
  sorry

end ReflexiveFixedPoints
end
end OAI
