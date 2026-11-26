-- Prove2me | Theorems.Thm_Kyprianou_Ch04_terminalCauchyFromCompactSupV1
-- name    : Kyprianou.Ch04.terminalCauchyFromCompactSupV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:04:20.16883+00:00
-- url     : https://prove2.me/theorems/bacf1543-c5c6-42b6-bf5b-1154b1bade46
-- title:
--   Terminal square Cauchy from compact squared supremum
-- statement:
--   Terminal square Cauchy from compact squared supremum.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem terminalCauchyFromCompactSupV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → NNReal → Ω → ℝ)
    (hi : ∀ a, 0 < a → a < 1 → ∀ t,
      Measurable (Y a t) ∧ Integrable (fun w => (Y a t w)^2) P)
    (hc : ∀ T : NNReal, 0 < T → ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ a b, 0 < a → a < r → 0 < b → b < r →
        (∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |Y a t w - Y b t w|^2) '' Iic T)) ∧
        Integrable (fun w => sSup ((fun t : NNReal => |Y a t w - Y b t w|^2) '' Iic T)) P ∧
        (∫ w, sSup ((fun t : NNReal => |Y a t w - Y b t w|^2) '' Iic T) ∂P) < δ) :
    ∀ t : NNReal, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ a b, 0 < a → a < r → 0 < b → b < r →
        (∫ w, (Y a t w - Y b t w)^2 ∂P) ≤ δ := by
  sorry
end Kyprianou.Ch04
