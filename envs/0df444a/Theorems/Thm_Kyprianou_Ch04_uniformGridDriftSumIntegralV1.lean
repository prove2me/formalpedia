-- Prove2me | Theorems.Thm_Kyprianou_Ch04_uniformGridDriftSumIntegralV1
-- name    : Kyprianou.Ch04.uniformGridDriftSumIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:24:00.933437+00:00
-- url     : https://prove2.me/theorems/ad0b6612-b6cf-5140-9e0a-f2c5b9b90b21
-- title:
--   Uniform drift grid sum equals integrated cell weights
-- statement:
--   A finite grid's weighted drift sum is the integral of its cellwise constant weights.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem uniformGridDriftSumIntegralV1 (T : NNReal) (n : ℕ) (H : NNReal → ℝ) :
    (∫ s in Ioc (0 : ℝ) (T : ℝ),
      ∑ i ∈ Finset.range (n+1),
        (Ioc ((T * (i : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal) : ℝ)
          ((T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal) : ℝ)).indicator
          (fun _ => H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal))) s) =
    ∑ i ∈ Finset.range (n+1),
      H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) *
      ((T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal -
        (T * (i : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal) := by
  sorry
end Kyprianou.Ch04
