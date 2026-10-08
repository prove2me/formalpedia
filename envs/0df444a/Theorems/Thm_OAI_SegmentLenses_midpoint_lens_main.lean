-- Prove2me | Theorems.Thm_OAI_SegmentLenses_midpoint_lens_main
-- name    : OAI.SegmentLenses.midpoint_lens_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:19.254933+00:00
-- url     : https://prove2.me/theorems/ac9e3323-df7d-4665-bd48-ca6f2c7a1357
-- statement:
--   The theorem states two parallel midpoint-lens inequalities in dual spaces built from segment-test norms. In each, a finite vertex set H is ancestral, meaning that whenever b lies in H and a is an ancestor of b, a also lies in H. For head H x, the coordinate functionals indexed by H are weighted by the values of x on the corresponding unit vectors and summed; tail H x is x minus this head. In the first part, the vertices are pairs (n, list of naturals) with n at least 1 and list length at most n, where a is an ancestor of b when they share n and the list of a is a prefix of the list of b. Here x and y lie in X, the full continuous dual of the completion of finitely supported real functions under the segment-test norm, and x equals its own head over H. For any R ≥ 0 with ‖x+y‖ ≤ R and ‖x−y‖ ≤ R, the conclusion is ‖tail H y‖ ≤ 2·√(R² − ‖x‖²), where the square root is Lean's real square root, which is zero for negative arguments. The second part is the same statement for vertices that are arbitrary finite lists of naturals, ordered by the prefix relation. There, x and y lie in the coordinate predual, the closure of the span of the coordinate functionals inside the full dual, x's underlying element equals its own head over H, and the conclusion bounds the norm of the tail of y's underlying element by the same quantity 2·√(R² − ‖x‖²). The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MidpointLenses.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MidpointLenses.lean; bytes 13144..13696
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MidpointLenses

namespace OAI

noncomputable section

open scoped BigOperators

open Finset

namespace SegmentLenses

theorem midpoint_lens_main :
    (∀ (H : Finset ForestVertex) (_ : Ancestral ForestAncestor H)
      (x y : X) (_ : x = head H x) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) ∧
    (∀ (H : Finset InfiniteVertex) (_ : Ancestral List.IsPrefix H)
      (x y : BInfinite) (_ : x.val = head H x.val) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y.val‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) :=
  sorry

end SegmentLenses
end
end OAI
