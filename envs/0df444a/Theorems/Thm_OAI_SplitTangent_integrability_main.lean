-- Prove2me | Theorems.Thm_OAI_SplitTangent_integrability_main
-- name    : OAI.SplitTangent.integrability_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:25.404145+00:00
-- url     : https://prove2.me/theorems/4c9bc0e0-deff-4095-b2d1-c07d935c7598
-- statement:
--   The theorem states that, for every complex manifold X (a Hausdorff, second countable space with a holomorphic atlas modeled on ℂ^d) that is connected, compact, and of complex dimension d ≥ 2, if X admits a projective embedding e and is rationally connected with respect to e, then every holomorphic splitting of its tangent bundle is integrable in both parts. A projective embedding is an injective map into some projective space ℙ^N(ℂ) such that each patch where homogeneous coordinate i is nonzero has open preimage, the affine coordinates there are holomorphic in x, and their derivative is injective at every point of the patch. Rational connectedness means there is a nonempty dense subset U of X×X, cut out as the nonvanishing locus of some family of bihomogeneous polynomials in the homogeneous coordinates of the two image points, such that every pair (x,y) in U is joined by a holomorphic rational curve, namely two holomorphic maps ℂ→X agreeing as f(z)=g(1/z) for z≠0, passing through x and y at two points of the Riemann sphere. A tangent splitting is a family of ℂ-linear idempotent endomorphisms P_x of each tangent space T_xX, depending holomorphically on x as a self-map of the tangent bundle, whose image and kernel both have positive complex dimension at every point. The conclusion is that both the image distribution x ↦ range P_x and the kernel distribution x ↦ ker P_x are integrable: on every open set U, whenever V and W are holomorphic vector fields on U taking values in the distribution, their Lie bracket also takes values in the distribution at every point of U.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SplitTangentIntegrability.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SplitTangentIntegrability.lean; bytes 5237..5306
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SplitTangentIntegrability

namespace OAI

noncomputable section

open scoped Manifold ContDiff LinearAlgebra.Projectivization

open Set Bundle

universe u

namespace SplitTangent

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

theorem integrability_main : IntegrabilityStatement.{u} := by
  sorry

end SplitTangent
end
end OAI
