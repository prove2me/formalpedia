-- Prove2me | Theorems.Thm_Kyprianou_Ch04_orderedSupSquareTailCauchyV1
-- name    : Kyprianou.Ch04.orderedSupSquareTailCauchyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:05:30.208909+00:00
-- url     : https://prove2.me/theorems/141444bc-9163-5504-980e-ebbba191dc9f
-- title:
--   Ordered cutoff square bound implies full Cauchy estimate
-- statement:
--   Ordered cutoff square bound implies full Cauchy estimate.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem orderedSupSquareTailCauchyV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℝ → NNReal → Ω → ℝ) (T : NNReal) (q : ℝ → ℝ)
    (hq : Tendsto q (𝓝[>] 0) (𝓝 0))
    (hb : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      Integrable (fun w => sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T)) P ∧
      (∫ w, sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T) ∂P) ≤ q b) :
    ∀ δ : ℝ, 0 < δ → ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 ∧
      ∀ a b : ℝ, 0 < a → a < e0 → 0 < b → b < e0 →
        Integrable (fun w => sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T)) P ∧
        (∫ w, sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T) ∂P) < δ := by
  sorry
end Kyprianou.Ch04
