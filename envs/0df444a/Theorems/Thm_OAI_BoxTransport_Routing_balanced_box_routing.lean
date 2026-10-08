-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_balanced_box_routing
-- name    : OAI.BoxTransport.Routing.balanced_box_routing
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:24.446516+00:00
-- url     : https://prove2.me/theorems/0d095288-e129-4ccf-abfe-8a21ae40aff4
-- statement:
--   The theorem states that for every natural number n, rational centers a_i, b_i in ℚ³ and rational positive half-widths h_i, k_i in ℚ³ (all coordinates strictly positive) indexed by i in Fin n, the following holds. Suppose the closed boxes {x ∈ ℝ³ : |x_j − (a_i)_j| ≤ (h_i)_j for all j} are pairwise disjoint over distinct indices, the target boxes with centers b_i and half-widths k_i are likewise pairwise disjoint, and each box pair is volume balanced, meaning the product over the three coordinates of k_i,j / h_i,j equals 1. Then there exist a vector field U on space-time ℝ × ℝ³ with values in ℝ³ and a map Φ : ℝ → ℝ³ → ℝ³ such that U is admissible, Φ is a global flow of U, and Φ delivers every box. Admissible means U is C^∞, compactly supported, spatially divergence-free at every time (the sum of the jth spatial derivatives of the jth component is zero), vanishes for all times t outside [1/4, 3/4], and is effective: there are computable procedures giving rational approximations, to any requested precision at rational space-time points, of every mixed partial derivative of U (taken along time or coordinate directions, in any finite list of axes), together with computable moduli of continuity and computable uniform bounds on these derivatives. Global flow means Φ(0,x) = x, each t ↦ Φ(t,x) is differentiable with derivative U(t, Φ(t,x)), and every differentiable curve γ starting at x with γ'(t) = U(t, γ(t)) coincides with Φ(·,x) for all t. Delivers means that for each i there is an open set containing the ith source box on which Φ(1,·) agrees with the coordinatewise affine map x_j ↦ (b_i)_j + (k_i,j / h_i,j)(x_j − (a_i)_j), which carries the source box onto the target box.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BalancedBoxRouting.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BalancedBoxRouting.lean; bytes 3188..3686
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BalancedBoxRouting

namespace OAI

open scoped BigOperators ContDiff

namespace BoxTransport.Routing

theorem balanced_box_routing
    (n : ℕ) (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) :
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a b h k Φ := by
  sorry

end BoxTransport.Routing
end OAI
