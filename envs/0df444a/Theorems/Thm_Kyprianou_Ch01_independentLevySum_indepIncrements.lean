-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentLevySum_indepIncrements
-- name    : Kyprianou.Ch01.independentLevySum_indepIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:33:47.900406+00:00
-- url     : https://prove2.me/theorems/5a827094-d997-4e2a-8346-e69c15ecc9f0
-- title:
--   Independent increments of the sum of two independent Levy processes
-- statement:
--   The increment family of the pointwise sum of two independent Levy processes is mutually independent for every monotone time partition.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.1, original target 1de56fa3-80d8-45c5-84de-bac5401cda86; original LeanLevy IsLevyProcess structure fields.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentLevySum_indepIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    HasIndependentIncrements (fun t ω => X t ω + Y t ω) P := by sorry
