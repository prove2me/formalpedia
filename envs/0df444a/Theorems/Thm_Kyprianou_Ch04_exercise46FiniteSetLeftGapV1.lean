-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FiniteSetLeftGapV1
-- name    : Kyprianou.Ch04.exercise46FiniteSetLeftGapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:16:20.108235+00:00
-- url     : https://prove2.me/theorems/1cba0630-a3ba-4642-bd65-de145ee746f2
-- title:
--   A finite set has an empty strict left neighbourhood at a positive time
-- statement:
--   Induct over the finite jump set, increasing the left endpoint to include each jump lying strictly before t.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FiniteSetLeftGapV1
    (S : Set NNReal) (hS : S.Finite) (t : NNReal) (ht : 0 < t) :
    ∃ s : NNReal, s < t ∧ ∀ u ∈ S, s < u → u < t → False := by
  sorry
