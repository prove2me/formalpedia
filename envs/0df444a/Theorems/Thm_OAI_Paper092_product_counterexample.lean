-- Prove2me | Theorems.Thm_OAI_Paper092_product_counterexample
-- name    : OAI.Paper092.product_counterexample
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:59.902006+00:00
-- url     : https://prove2.me/theorems/e5e5b465-dd60-42e2-bcbc-24af2372354c
-- statement:
--   The theorem states that, in 20-dimensional Euclidean space, the set productWitness, consisting of points whose first ten coordinates and last ten coordinates each lie in the standard simplex of dimension 10 (the convex hull of the origin and the ten standard basis vectors), satisfies several claims. First, it is compact, convex, and has nonempty interior. Second, its normalized projection volume, defined as vol(projectionBody K)/vol(K)^(n-1) with n=20, where the projection body is the set of y with <u,y> at most the brightness of u for every u, and brightness is |u| times the volume of the orthogonal projection of K onto the hyperplane normal to u, divided by the simplex constant simplexConstant(20)=21*20^20/20!, equals 121*C(20,10)/(21*2^20). Third, this ratio equals 22355476/22020096. Fourth, the ratio is strictly greater than 1. Fifth, the real-valued volume of the projection body of productWitness is strictly greater than simplexConstant(20) times the real-valued volume of productWitness raised to the power 19. The theorem is admitted in the source, not proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProjectionVolume.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProjectionVolume.lean; bytes 1492..2083
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ProjectionVolume

namespace OAI

noncomputable section

open Set MeasureTheory

open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem product_counterexample :
    (IsCompact productWitness ∧ Convex ℝ productWitness ∧
      (interior productWitness).Nonempty) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 ∧
    1 < normalizedProjectionVolume productWitness / simplexConstant 20 ∧
    (volume (projectionBody productWitness)).toReal >
      simplexConstant 20 * (volume productWitness).toReal ^ 19 := by
  sorry

end Paper092
end
end OAI
