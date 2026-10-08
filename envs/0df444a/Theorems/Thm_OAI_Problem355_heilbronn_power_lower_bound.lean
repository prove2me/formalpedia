-- Prove2me | Theorems.Thm_OAI_Problem355_heilbronn_power_lower_bound
-- name    : OAI.Problem355.heilbronn_power_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:10.981698+00:00
-- url     : https://prove2.me/theorems/0ca11482-9e69-4802-a402-56069b7294ad
-- statement:
--   The theorem states that the Heilbronn exponent δ is positive and that there exist a sequence of natural numbers n(j) tending to infinity and finite sets P(j) of points in the plane, such that for every j, n(j) ≥ 3, P(j) has exactly n(j) points, all lying in the closed unit square [0,1]×[0,1], and every triple of three distinct points of P(j) spans a triangle of area at least n(j)^(−2+δ). Triangle area is |(q₁−p₁)(r₂−p₂)−(q₂−p₂)(r₁−p₁)|/2. Here δ = 1/(100000·K) with K = T²+1, where T = C(M,3), M = C(4·41−1, 41) = C(163,41), so δ is an explicit but extremely small positive rational constant. Thus the statement asserts an infinite family of point sets whose smallest triangle area is at least a power n^(−2+δ).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HeilbronnTriangle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HeilbronnTriangle.lean; bytes 1460..1824
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HeilbronnTriangle

namespace OAI

noncomputable section

namespace Problem355

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

theorem heilbronn_power_lower_bound :
    0 < heilbronnExponent ∧ ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
      Filter.Tendsto n Filter.atTop Filter.atTop ∧ ∀ j : ℕ,
        3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
        triangleAreasAtLeast (P j)
          (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  sorry

end Problem355
end
end OAI
