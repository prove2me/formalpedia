-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagCompMonotoneClockV1
-- name    : Kyprianou.Ch02.cadlagCompMonotoneClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:32:27.184657+00:00
-- url     : https://prove2.me/theorems/f090fe50-d239-4b79-8a84-480be8efe2b4
-- title:
--   cadlagCompMonotoneClock
-- statement:
--   cadlagCompMonotoneClock
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagCompMonotoneClockV1
    (f : ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ≥0)
    (hf : ProbabilityTheory.IsCadlag f)
    (hg : ProbabilityTheory.IsCadlag (fun t => (g t : ℝ)))
    (hm : Monotone g) :
    ProbabilityTheory.IsCadlag (fun t => f (g t)) := by sorry
