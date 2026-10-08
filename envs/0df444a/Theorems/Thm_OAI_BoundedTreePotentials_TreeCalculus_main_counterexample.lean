-- Prove2me | Theorems.Thm_OAI_BoundedTreePotentials_TreeCalculus_main_counterexample
-- name    : OAI.BoundedTreePotentials.TreeCalculus.main_counterexample
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:24.153915+00:00
-- url     : https://prove2.me/theorems/bc804a01-b715-46a1-84a1-f2ed49a16a7a
-- statement:
--   The theorem states that, for every choice of a Boolean flag r (whether the root node, the empty list, is included as a coordinate) and every quadratic kind k among sibling, antichain and global, the following hold for the Banach space X = TestCompletion(treeTestFamily r k). Here nodes are finite lists of natural numbers, the potential of a coefficient function f at a node s is the sum of f over all prefixes of s, and a coefficient function f is a tree test if f vanishes at the root when r is false, every potential satisfies |potential f s| ≤ 1, a quadratic budget holds, and a support condition holds. The budget says that the sum of f(s)² over every admissible finite set B of nodes is at most 1, where admissible means: all of B are children of one common parent (sibling), pairwise prefix-incomparable (antichain), or any finite set (global). The support condition is vacuous for sibling, finite support for antichain, and square-summability for global. The tree test family is the set of such functions on the coordinates, and each finitely supported vector x is given the norm sup over tests f of |Σ x_i f_i|; X is the completion of this normed space. First, X is complete, separable, and not finite-dimensional over ℝ. Second, for every 0 < t < 1, the averaged modulus of X, defined as the infimum over unit vectors x of the supremum over closed finite-codimension subspaces F of the infimum over y in F with ‖y‖ ≥ 1 of (‖x+ty‖+‖x−ty‖)/2 − 1, is at least √(1+t²/4) − 1. Third, for every real normed space Y that is linearly homeomorphic to X, Y does not satisfy IsAUCReal, meaning it is false that the one-sided modulus (defined like the averaged one but with ‖y‖ = 1 and the quantity ‖x+ty‖ − 1) is positive for every t > 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BoundedTreePotentials.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BoundedTreePotentials.lean; bytes 14216..14826
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BoundedTreePotentials

namespace OAI

noncomputable section

universe u

open Set

open scoped ENNReal Classical

namespace BoundedTreePotentials

open TreeCalculus in
theorem TreeCalculus.main_counterexample (r : Bool) (k : QuadraticKind) :
    (CompleteSpace (TestCompletion (treeTestFamily r k)) ∧
      TopologicalSpace.SeparableSpace (TestCompletion (treeTestFamily r k)) ∧
      ¬Module.Finite ℝ (TestCompletion (treeTestFamily r k))) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      Real.sqrt (1 + t ^ 2 / 4) - 1 ≤
        averagedModulusReal (TestCompletion (treeTestFamily r k)) t) ∧
    (∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℝ Y],
      (TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) → ¬IsAUCReal Y) := by
  sorry

end BoundedTreePotentials
end
end OAI
