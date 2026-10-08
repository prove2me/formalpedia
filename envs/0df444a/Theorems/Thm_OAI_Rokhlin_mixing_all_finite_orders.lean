-- Prove2me | Theorems.Thm_OAI_Rokhlin_mixing_all_finite_orders
-- name    : OAI.Rokhlin.mixing_all_finite_orders
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:16.683349+00:00
-- url     : https://prove2.me/theorems/598dcbcb-a509-4bad-ab4e-67bcece5c6bd
-- statement:
--   The theorem states that an invertible measurable transformation T of a probability space (Ω, μ), with measurable inverse and preserving μ, is mixing of every finite order k ≥ 3 whenever it is mixing: for all measurable A and B, μ(A ∩ (Tⁿ)⁻¹(B)) → μ(A)μ(B) as |n| → ∞ through integers. Specifically, for any k ≥ 3 and measurable sets A₀, …, Aₖ₋₁, set t₀ = 0 and tᵢ = g₀ + ⋯ + gᵢ₋₁, where the gaps gⱼ are positive integers. Then the measure of the intersection of the inverse images (T^{tᵢ})⁻¹(Aᵢ), for 0 ≤ i < k, tends to the product of the measures μ(Aᵢ) as every gap tends to infinity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Rokhlin.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Rokhlin.lean; bytes 941..1167
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_Rokhlin

namespace OAI

open MeasureTheory Filter

open scoped BigOperators Topology

namespace Rokhlin

variable {Ω : Type*} [MeasurableSpace Ω]

theorem mixing_all_finite_orders (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (h_pres : MeasurePreserving T μ μ) (h_mix : IsMixing μ T) :
    ∀ k : ℕ, 3 ≤ k → MixingOfOrder μ T k := by
  sorry

end Rokhlin
end OAI
