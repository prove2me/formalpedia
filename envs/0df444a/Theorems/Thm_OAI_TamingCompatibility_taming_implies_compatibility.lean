-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_taming_implies_compatibility
-- name    : OAI.TamingCompatibility.taming_implies_compatibility
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.186357+00:00
-- url     : https://prove2.me/theorems/b73db3a1-40a3-4d92-8133-42bb4a296c0f
-- statement:
--   The theorem states that, for a smooth manifold X modeled on four-dimensional Euclidean space ℝ⁴ (charted with smooth transition maps) that is Hausdorff, second countable, compact and connected, and for an almost complex structure J on X, if some symplectic two-form α tames J, then there exists a symplectic two-form η that is compatible with J. Here a two-form assigns to each point x a continuous alternating real bilinear form on the tangent space at x, and an almost complex structure J is a smooth field of continuous linear endomorphisms of the tangent spaces with J(Jv) = −v for every tangent vector v. A two-form is symplectic when it is smooth (its pullbacks along smooth maps from open subsets of ℝ⁴ are smooth), closed (the exterior derivative of each such pullback vanishes), and nondegenerate (a tangent vector v with α(v,w) = 0 for all w must be zero). The form α tames J when α(v, Jv) > 0 for every nonzero tangent vector v at every point. The form η is compatible with J when it tames J and is J-invariant, meaning η(Ju, Jv) = η(u, v) for all tangent vectors u and v at every point. This is a formal statement admitted without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TamingCompatibility.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TamingCompatibility.lean; bytes 2074..2362
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TamingCompatibility

namespace OAI

noncomputable section

open scoped Manifold ContDiff

namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

theorem taming_implies_compatibility
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X]
    (J : AlmostComplexStructure X)
    (h : ∃ α : TwoForm X, IsSymplectic α ∧ Tames α J) :
    ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J := by
  sorry

end TamingCompatibility
end
end OAI
