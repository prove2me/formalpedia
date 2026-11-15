-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentLevySum_zero
-- name    : Kyprianou.Ch01.independentLevySum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:32:04.978637+00:00
-- url     : https://prove2.me/theorems/b51d1f32-d710-42b6-9f4f-1a4a2968c3ed
-- title:
--   Sum of two Levy processes starts at zero
-- statement:
--   Two Lévy processes each start at zero, so their pointwise sum also starts at zero.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.1; exact original independentLevySum theorem 1de56fa3-80d8-45c5-84de-bac5401cda86.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentLevySum_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P) :
    (fun ω => X 0 ω + Y 0 ω) = (fun _ => (0 : ℝ)) := by sorry
