-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_S_zero
-- name    : Kyprianou.Ch04.kw48_S_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:42:35.299921+00:00
-- url     : https://prove2.me/theorems/f9a50713-ce59-4bc1-a751-8dcb0e718a5d
-- title:
--   Initial record-level primitive vanishes
-- statement:
--   Initial record-level primitive vanishes.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The record-level primitive vanishes at the initial time. -/

theorem Kyprianou.Ch04.kw48_S_zero {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω) :
    S L beta 0 w = 0 := by sorry
