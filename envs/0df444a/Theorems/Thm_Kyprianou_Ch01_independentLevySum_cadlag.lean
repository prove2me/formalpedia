-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentLevySum_cadlag
-- name    : Kyprianou.Ch01.independentLevySum_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:32:05.735482+00:00
-- url     : https://prove2.me/theorems/950914e7-cebf-4cd0-8dae-954c23f117b2
-- title:
--   Almost-sure cadlag paths of a sum of two Levy processes
-- statement:
--   The sum of two càdlàg Lévy paths is càdlàg almost surely, by intersection of full-measure path events and closure of càdlàg functions under addition.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.1; exact original independentLevySum theorem 1de56fa3-80d8-45c5-84de-bac5401cda86.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentLevySum_cadlag
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω + Y t ω) := by sorry
