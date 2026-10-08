-- Prove2me | Theorems.Thm_OAI_AllScaleInverseVolume_inverse_volume_without_support
-- name    : OAI.AllScaleInverseVolume.inverse_volume_without_support
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:20.747734+00:00
-- url     : https://prove2.me/theorems/5618cee2-64cf-4daf-a584-a923b2d1980e
-- statement:
--   The theorem states that there exist a real constant C > 0 and an integer d₀ such that, for every integer d ≥ d₀, the following holds. Let ν be any probability measure on d-dimensional real Euclidean space satisfying ν(B(x,r)) ≤ r^((d−1)/2) for every center x and every radius r > 0, where B(x,r) is the open Euclidean ball. Put k = ⌊d/100⌋. For every vector u, sample z₁, …, zₖ independently from ν and let V be the square root of the determinant of their Gram matrix (⟨zᵢ−u,zⱼ−u⟩)ᵢⱼ, the k-dimensional parallelepiped volume of these displacement vectors. Then the extended nonnegative expectation of (V⁻¹)ᵏ is at most exp(Cdk). The inverse and expectation are taken in the extended nonnegative reals, so zero volume yields an infinite inverse. No bounded-support assumption is imposed on ν.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianInformation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianInformation.lean; bytes 6220..6297
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianInformation_002

namespace OAI

open MeasureTheory ProbabilityTheory Set

open scoped BigOperators ENNReal

open MeasureTheory Metric

open scoped ENNReal

namespace AllScaleInverseVolume

attribute [local instance] _root_.OAI.AllScaleInverseVolume.namedAtLeastTwoTwo

attribute [local instance] _root_.OAI.AllScaleInverseVolume.ambientSub

attribute [local instance] _root_.OAI.AllScaleInverseVolume.ambientInner

theorem inverse_volume_without_support : InverseVolumeStatement := by
  sorry

end AllScaleInverseVolume
end OAI
