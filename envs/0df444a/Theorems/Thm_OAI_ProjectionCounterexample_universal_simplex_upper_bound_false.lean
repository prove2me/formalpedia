-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_universal_simplex_upper_bound_false
-- name    : OAI.ProjectionCounterexample.universal_simplex_upper_bound_false
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:11.819418+00:00
-- url     : https://prove2.me/theorems/d6310adc-8190-4f4b-a5ff-19de7d8afc16
-- statement:
--   The theorem states that, in 20-dimensional Euclidean space, it is false that every convex body P satisfies ratio(P) ≤ ratio(simplex). Here a convex body is a compact convex set with nonempty interior, and the simplex is the convex hull of the origin and the 20 standard basis vectors. For a unit vector u, the projection volume of P is the (d−1)-dimensional Euclidean Hausdorff measure, with d=20, of the image of P under orthogonal projection onto the hyperplane orthogonal to u, taken as a real number. The projection body of P is the set of points x such that ⟨u,x⟩ is at most this projection volume for every unit vector u. The ratio of P is the Lebesgue volume of its projection body divided by the volume of P raised to the power d−1=19. So the theorem asserts that some convex body P in dimension 20 has ratio(P) strictly greater than ratio of the simplex. The source proof is admitted rather than verified here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProjectionCounterexample.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProjectionCounterexample.lean; bytes 1141..1279
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Definitions.Def_ProjectionCounterexample

namespace OAI

noncomputable section

open Set MeasureTheory

open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem universal_simplex_upper_bound_false :
    ¬ (∀ P : Set (E 20), IsConvexBody P → ratio P ≤ ratio (simplex 20)) := by
  sorry

end ProjectionCounterexample
end
end OAI
