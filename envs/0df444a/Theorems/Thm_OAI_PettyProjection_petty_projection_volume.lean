-- Prove2me | Theorems.Thm_OAI_PettyProjection_petty_projection_volume
-- name    : OAI.PettyProjection.petty_projection_volume
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:03.224422+00:00
-- url     : https://prove2.me/theorems/9f028a1b-b20a-4967-83a5-61322a33ca81
-- statement:
--   The theorem states that for every integer n ≥ 4 and every convex body K in Euclidean space ℝⁿ (a compact convex set with nonempty interior), the projection ratio of K is at least the Petty constant, and equality holds exactly when K is an ellipsoid. Here the shadow volume of K in a unit direction u is the (n−1)-dimensional volume of the orthogonal projection of K onto the hyperplane u^⊥, with volume taken in the induced Euclidean structure. The projection body of K is the set of points x with ⟨u,x⟩ ≤ shadowVolume(K,u) for every unit vector u. The projection ratio is vol(projection body of K) divided by vol(K)^(n−1). The Petty constant is κ(n−1)ⁿ · κ(n)^(2−n), where κ(m) is the volume of the closed unit ball in ℝ^m. An ellipsoid means a set of the form {a + T x : ‖x‖ ≤ 1} for some vector a and invertible linear map T of ℝⁿ. So the statement is that pettyConstant(n) ≤ projectionRatio(K), with projectionRatio(K) = pettyConstant(n) if and only if K is an ellipsoid.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PettyProjectionVolume.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PettyProjectionVolume.lean; bytes 1425..1734
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PettyProjectionVolume

namespace OAI

noncomputable section

open Set MeasureTheory

open scoped RealInnerProductSpace

namespace PettyProjection

/-- The exact unrestricted inequality and its global equality characterization.
-/
theorem petty_projection_volume (n : ℕ) (hn : 4 ≤ n)
    (K : Set (Space n)) (hK : IsConvexBody K) :
    pettyConstant n ≤ projectionRatio K ∧
      (projectionRatio K = pettyConstant n ↔ IsEllipsoid K) := by
  sorry

end PettyProjection
end
end OAI
