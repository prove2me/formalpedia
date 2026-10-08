-- Prove2me | Theorems.Thm_OAI_TriangularBilliards_irrational_triangle_billiard
-- name    : OAI.TriangularBilliards.irrational_triangle_billiard
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:34.738793+00:00
-- url     : https://prove2.me/theorems/dfc2bbdb-1c6c-4f6d-b076-f5b7643346ef
-- statement:
--   The theorem states that for any triangle Q in the complex plane, given by three affinely independent vertices, if at least one interior angle of Q is an irrational multiple of π (the angle at some vertex divided by π is irrational), then the main conclusion holds for Q. That conclusion concerns the billiard flow on the phase space ℂ × Circle, with probability measure given by normalized area on the open interior of the triangle times uniform angular measure on the circle. It asserts that the phase measure of the whole space is 1; that almost every phase point admits a complete flight chain, meaning a bi-infinite sequence of collisions at times unbounded in both directions, each at a point in the open interior of a side and never at a vertex, with straight-line motion strictly inside the table between collisions, the initial time lying strictly inside flight zero, and specular reflection of the direction at each collision; that for each phase point any two flight chains coincide; that for every real t the time-t billiard flow (defined by these chains, and by the identity at points with no chain) preserves the phase measure; that the flow is a group action almost everywhere, so the time s+t map agrees almost everywhere with the composition of the time s and time t maps; and that every measurable set A whose preimage under every time-t map differs from A by a null set has measure 0 or 1, which is ergodicity of the flow.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IrrationalTriangleBilliard.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IrrationalTriangleBilliard.lean; bytes 4882..4998
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_IrrationalTriangleBilliard

namespace OAI

open MeasureTheory Set

open scoped ENNReal symmDiff

noncomputable section

namespace TriangularBilliards

theorem irrational_triangle_billiard (Q : Triangle) (hQ : Q.HasIrrationalAngle) :
    MainConclusion Q := by
  sorry

end TriangularBilliards
end
end OAI
