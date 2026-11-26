-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactSquareSupProbabilityV1
-- name    : Kyprianou.Ch04.compactSquareSupProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:17.747839+00:00
-- url     : https://prove2.me/theorems/21b0c32f-a78b-4e73-93ee-b564b5393e25
-- title:
--   Markov inequality for compact path supremum
-- statement:
--   Markov inequality for compact path supremum.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compactSquareSupProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : NNReal → Ω → ℝ) (T : NNReal) (d : ℝ) (hd : 0 < d)
    (hb : ∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |Y t w|^2) '' Iic T))
    (hi : Integrable (fun w => sSup ((fun t : NNReal => |Y t w|^2) '' Iic T)) P) :
    P {w | ∃ t ≤ T, d < |Y t w|} ≤
      ENNReal.ofReal (∫ w, sSup ((fun t : NNReal => |Y t w|^2) '' Iic T) ∂P) /
        ENNReal.ofReal (d^2) := by
  sorry
end Kyprianou.Ch04
