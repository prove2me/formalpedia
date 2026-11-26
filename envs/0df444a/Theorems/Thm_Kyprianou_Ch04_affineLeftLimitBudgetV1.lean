-- Prove2me | Theorems.Thm_Kyprianou_Ch04_affineLeftLimitBudgetV1
-- name    : Kyprianou.Ch04.affineLeftLimitBudgetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:58:09.19086+00:00
-- url     : https://prove2.me/theorems/c07b8641-072a-49ab-b053-db108a7c5976
-- title:
--   Left-limit square budget from two finite affine step paths
-- statement:
--   Left-limit square budget from two finite affine step paths
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem affineLeftLimitBudgetV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V UL VL : NNReal → Ω → ℝ) (d e : ℝ) (T : NNReal)
    (hU : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ (L S : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) → U t ω = d * (t : ℝ) +
        (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) +
        (∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0))
    (hV : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ (L S : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) → V t ω = e * (t : ℝ) +
        (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) +
        (∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0))
    (hUL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => U s ω) (𝓝[<] t) (𝓝 (UL t ω)))
    (hVL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => V s ω) (𝓝[<] t) (𝓝 (VL t ω))) :
    ∀ᵐ ω ∂P,
      let Q := sSup ((fun t : NNReal => |U t ω - V t ω|^2) '' Iic T)
      0 ≤ Q ∧ ∀ t : NNReal, 0 < t → t ≤ T → (UL t ω - VL t ω)^2 ≤ Q := by
  sorry
end Kyprianou.Ch04
