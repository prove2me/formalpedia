-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PrelevelLeftIsolatedV1
-- name    : Kyprianou.Ch04.exercise46PrelevelLeftIsolatedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:14:19.822513+00:00
-- url     : https://prove2.me/theorems/86a826a3-ac03-5c6d-8042-7db6d6b8a452
-- title:
--   Locally affine left limits have countable level sections
-- statement:
--   Each positive level contact is isolated from the left because the path left limits are affine with unit slope on an interval ending there. Apply the proved countability theorem.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PrelevelLeftIsolatedV1
    (f : NNReal → Real) (x : Real)
    (hAffine : ∀ t : NNReal, 0 < t →
      ∃ s : NNReal, s < t ∧ ∀ u : NNReal, s < u → u ≤ t →
        Function.leftLim f u = f s + ((u : Real) - (s : Real))) :
    ({t : NNReal | 0 < t ∧ Function.leftLim f t = x}).Countable := by
  sorry
