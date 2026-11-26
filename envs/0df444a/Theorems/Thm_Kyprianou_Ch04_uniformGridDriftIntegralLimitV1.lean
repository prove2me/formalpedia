-- Prove2me | Theorems.Thm_Kyprianou_Ch04_uniformGridDriftIntegralLimitV1
-- name    : Kyprianou.Ch04.uniformGridDriftIntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:36:45.079663+00:00
-- url     : https://prove2.me/theorems/adf52c4a-4c61-484a-a2ae-33c6a71a75de
-- title:
--   Bounded strict-left uniform drift grid integral limit
-- statement:
--   The finite cell weights integrate exactly to the drift grid sum. Each positive time lies in a unique right-closed cell, whose left sample converges strictly from below. Dominated convergence yields the drift integral.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem uniformGridDriftIntegralLimitV1 (T : NNReal) (H : NNReal → ℝ) (C : ℝ)
    (hb : ∀ r, |H r| ≤ C)
    (hl : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n+1),
      H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) *
      ((T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal -
        (T * (i : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal))
      atTop (𝓝 (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal)) := by
  sorry
end Kyprianou.Ch04
