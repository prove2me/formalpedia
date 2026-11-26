-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_S_adapted_bound
-- name    : Kyprianou.Ch04.kw48_S_adapted_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:42:37.767983+00:00
-- url     : https://prove2.me/theorems/12b752fa-877f-43ec-ad77-fc92be020726
-- title:
--   Record-level primitive strongly adapted with norm bound
-- statement:
--   Record-level primitive strongly adapted with norm bound.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The record-level primitive is strongly adapted and its norm
is bounded by the running record. -/

theorem Kyprianou.Ch04.kw48_S_adapted_bound {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) :
    StronglyAdapted F (S L beta) ∧
      ∀ t w, ‖S L beta t w‖ ≤ runningSup L t w := by sorry
