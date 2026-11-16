-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentLevySum
-- name    : Kyprianou.Ch01.independentLevySum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:18:20.043645+00:00
-- url     : https://prove2.me/theorems/1de56fa3-80d8-45c5-84de-bac5401cda86
-- title:
--   Exercise 1.1: independent sum of two Lévy processes is a Lévy process
-- statement:
--   From Kyprianou Definition 1.1, prove that the independent sum of two real-valued Lévy processes remains Lévy. The independence hypothesis is on the whole paths, ensuring increments of each process and across the processes are jointly independent. The result supports the Lévy–Itô construction of Theorem 1.6. The arbitrary finite-sum induction is a later corollary. This is a draft theorem awaiting remote Lean elaboration.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.1, printed p. 26.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentLevySum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    IsLevyProcess (fun t ω => X t ω + Y t ω) P := by
  sorry
