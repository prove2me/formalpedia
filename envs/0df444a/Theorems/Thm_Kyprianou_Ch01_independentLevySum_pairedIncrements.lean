-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentLevySum_pairedIncrements
-- name    : Kyprianou.Ch01.independentLevySum_pairedIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:25:55.897103+00:00
-- url     : https://prove2.me/theorems/939d645d-5037-4738-866d-3495e3786308
-- title:
--   Joint independent-increment pairs of independent Lévy processes
-- statement:
--   For any monotone finite time grid, the pairs of increments from two independent Lévy processes form a mutually independent family, using independence within each process and between the complete paths.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.1, intermediate independence-of-paired-increments lemma.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentLevySum_pairedIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      iIndepFun
        (fun k : Fin n => fun ω =>
          (increment X (t k.castSucc) (t k.succ) ω,
           increment Y (t k.castSucc) (t k.succ) ω)) P := by sorry
