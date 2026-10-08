-- Prove2me | Theorems.Thm_OAI_DirectionalZeroOne_directional_zero_one
-- name    : OAI.DirectionalZeroOne.directional_zero_one
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:35.412682+00:00
-- url     : https://prove2.me/theorems/025048e5-a5fd-4c87-b902-25af24b3e0f7
-- statement:
--   The theorem states that, for every dimension d ≥ 3, a random walk in an i.i.d. random environment on the lattice ℤ^d obeys a directional zero-one law. Here a row at a site is a probability vector p on the 2d nearest-neighbour steps (coordinate direction i in Fin d, sign + or −), with each p(e) in [0,1] and the entries summing to 1. The environment assigns an independent row to every site, each drawn from a probability measure μ on rows, and the strict ellipticity hypothesis on μ says that μ-almost every row gives every one of the 2d steps strictly positive probability. Given the environment, the walker at site x moves to x plus the unit vector of step e with probability p_x(e); the annealed law of the path started at 0 averages over both the environment and the walk. For any nonzero real vector ℓ in ℝ^d, the escape event is that the path X satisfies Σᵢ Xₙ(i)·ℓᵢ → +∞ as n → ∞, that is, the walk tends to infinity in the direction ℓ. The conclusion is that the annealed probability of this event, starting from 0, is either exactly 0 or exactly 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectionalWalk.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectionalWalk.lean; bytes 3089..3354
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DirectionalWalk

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder

open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

theorem directional_zero_one (d : ℕ) (hd : 3 ≤ d)
    (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (ℓ : Fin d → ℝ) (hℓ : ℓ ≠ 0) :
    annealed μ 0 (escape ℓ) = 0 ∨ annealed μ 0 (escape ℓ) = 1 := by sorry

end DirectionalZeroOne
end OAI
