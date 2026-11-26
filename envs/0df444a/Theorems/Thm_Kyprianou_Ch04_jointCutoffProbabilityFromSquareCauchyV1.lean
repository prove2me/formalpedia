-- Prove2me | Theorems.Thm_Kyprianou_Ch04_jointCutoffProbabilityFromSquareCauchyV1
-- name    : Kyprianou.Ch04.jointCutoffProbabilityFromSquareCauchyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:05:29.956487+00:00
-- url     : https://prove2.me/theorems/aace35bf-4aea-59d3-81ec-097fd5414267
-- title:
--   Joint probability Cauchy estimate from compact square bounds
-- statement:
--   Joint probability Cauchy estimate from compact square bounds.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem jointCutoffProbabilityFromSquareCauchyV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : ℝ → NNReal → Ω → ℝ)
    (hC : ∀ W ∈ ({U,V} : Set (ℝ → NNReal → Ω → ℝ)), ∀ T : NNReal, 0 < T →
      ∀ δ : ℝ, 0 < δ → ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 ∧
        ∀ a b : ℝ, 0 < a → a < e0 → 0 < b → b < e0 →
          (∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |W a t w - W b t w|^2) '' Iic T)) ∧
          Integrable (fun w => sSup ((fun t : NNReal => |W a t w - W b t w|^2) '' Iic T)) P ∧
          (∫ w, sSup ((fun t : NNReal => |W a t w - W b t w|^2) '' Iic T) ∂P) < δ) :
    ∀ i : ℕ, ∃ J : ℕ, ∀ m n, J ≤ m → J ≤ n →
      P {w | ∃ t ≤ (i : NNReal), (2⁻¹ : ℝ)^i <
        dist (U (1 / ((m : ℝ)+2)) t w,V (1 / ((m : ℝ)+2)) t w)
          (U (1 / ((n : ℝ)+2)) t w,V (1 / ((n : ℝ)+2)) t w)} ≤ (2⁻¹ : ENNReal)^i := by
  sorry
end Kyprianou.Ch04
