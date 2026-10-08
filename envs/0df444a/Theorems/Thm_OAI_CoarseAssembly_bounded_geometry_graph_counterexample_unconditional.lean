-- Prove2me | Theorems.Thm_OAI_CoarseAssembly_bounded_geometry_graph_counterexample_unconditional
-- name    : OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:27.081313+00:00
-- url     : https://prove2.me/theorems/8e41c6a0-ddcf-45e8-88ac-38b944d2b7fc
-- statement:
--   The theorem states that, for the concrete construction in the file, the following all hold. For each j, the fiber vertex type FiberVertex j (pairs of a point u of the triangular-lattice disc of radius j and an element of SL₃(ℤ/2^k), where k = j minus the radius of u) is finite, and the fibered graph on it, with moves given by the elementary-matrix generators of SL₃(ℤ) (with their inverses and the identity) and the chosen holonomy unit t of ℤ₂ (a transcendental principal unit), is connected. There is a single natural number D bounding the degree of every vertex in every fibered graph. On the union of all these fibers, VertexUnion, with the metric built from these graphs, the space is proper, has uniformly finite balls (for each R ≥ 0 there is N such that every closed ball of radius R has at most N points), and distinct points are at distance at least 1. Finally, there is a class α in the coarse homology group KX₁ of VertexUnion such that nα ≠ 0 for every nonzero integer n, yet the constructed coarse assembly map to K₁ of the Roe algebra sends α to 0, and also 1 ⊗ α ≠ 0 in ℚ ⊗ KX₁. Hence the assembly map is not injective, and it remains non-injective after tensoring with ℚ. The source declares this theorem with sorry, so no proof is claimed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoarseAssembly.lean; bytes 338137..338902
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CoarseAssembly

open scoped Topology

namespace OAI

section

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] _root_.OAI.CoarseAssembly.unconditionalConclusionMetric

theorem bounded_geometry_graph_counterexample_unconditional :
    (∀ j, Finite (FiberVertex j) ∧
      (fiberedGraph elementaryMoves chosenHolonomyUnit j).Connected) ∧
    (∃ D : ℕ, ∀ j (x : FiberVertex j),
      Nat.card {y // (fiberedGraph elementaryMoves chosenHolonomyUnit j).Adj x y} ≤ D) ∧
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ constructedCoarseAssembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective constructedCoarseAssembly ∧
        ¬ Function.Injective (constructedCoarseAssembly.toIntLinearMap.lTensor ℚ) := by
  sorry

end CoarseAssembly
end
end
end OAI
