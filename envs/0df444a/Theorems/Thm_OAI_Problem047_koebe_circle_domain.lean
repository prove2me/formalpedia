-- Prove2me | Theorems.Thm_OAI_Problem047_koebe_circle_domain
-- name    : OAI.Problem047.koebe_circle_domain
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:06.407419+00:00
-- url     : https://prove2.me/theorems/877b63ab-8c54-406e-beb7-0ae55b071c0b
-- statement:
--   The theorem is admitted without proof and states that for every open connected subset U of the Riemann sphere (the one-point compactification of ℂ), there exist a subset V of the sphere and a map f from the sphere to itself such that V is a circle domain and f is a conformal equivalence from U onto V. A circle domain is an open connected set whose complement has every connected component (taken in the complement) either a single point or a round closed disk, meaning the image of the closed unit disk in ℂ under some Möbius transformation in GL₂(ℂ). A conformal equivalence f from U to V means f is conformal at every point of U, maps U into V, and has an inverse map g that is conformal at every point of V, maps V into U, and satisfies g(f(z))=z on U and f(g(w))=w on V. Conformality at a point p means f is continuous there and, in the standard charts at p and f(p) (using the inversion coordinate at ∞), the transported map has a nonzero complex derivative at p. U is not required to have any special complement, so the claim is Koebe's circle-domain uniformization for arbitrary domains in the sphere.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KoebeCircleDomains.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KoebeCircleDomains.lean; bytes 2028..2236
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_KoebeCircleDomains

namespace OAI

noncomputable section

open Set Classical

open scoped OnePoint

open CircleDomainRigidity

namespace Problem047

theorem koebe_circle_domain :
    ∀ U : Set Sphere, IsOpen U → IsConnected U →
      ∃ (V : Set Sphere) (f : Sphere → Sphere),
        IsCircleDomain V ∧ IsConformalEquivalence f U V := by
  sorry

end Problem047
end
end OAI
