-- Prove2me | Theorems.Thm_Kyprianou_Ch04_uniformGridRightClosedCellExistsV1
-- name    : Kyprianou.Ch04.uniformGridRightClosedCellExistsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:24:05.245049+00:00
-- url     : https://prove2.me/theorems/2efaba10-63b1-4e62-9de6-9298eaf45aff
-- title:
--   Uniform grid right-closed cell existence
-- statement:
--   Every positive time on a compact horizon belongs to a uniform right-closed cell.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem uniformGridRightClosedCellExistsV1 (T r : NNReal) (hr : 0 < r) (hrT : r ≤ T) (n : ℕ) :
    ∃ i : ℕ, i < n+1 ∧ T * (i : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
      r ≤ T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) := by
  sorry
end Kyprianou.Ch04
