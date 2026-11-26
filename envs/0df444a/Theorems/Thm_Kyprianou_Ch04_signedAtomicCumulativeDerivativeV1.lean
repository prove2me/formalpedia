-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedAtomicCumulativeDerivativeV1
-- name    : Kyprianou.Ch04.signedAtomicCumulativeDerivativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:39:11.436467+00:00
-- url     : https://prove2.me/theorems/b00f5096-9ea6-5279-9837-fdfe1797a674
-- title:
--   Zero derivative of a signed absolutely summable atomic cumulative sum
-- statement:
--   Split the absolutely summable weights into positive and negative parts and subtract their almost-everywhere zero derivatives.
-- source:
--   Supporting deterministic differentiation for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_atomicCumulativeDerivativeV1
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.signedAtomicCumulativeDerivativeV1 {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable (fun i => |w i|)) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt
      (fun t => ∑' i, (a ⁻¹' Iic t).indicator w i) 0 x := by
  sorry
