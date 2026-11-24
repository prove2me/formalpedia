-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectedDenseSupFunctionalV1
-- name    : Kyprianou.Ch03.reflectedDenseSupFunctionalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:00:55.481733+00:00
-- url     : https://prove2.me/theorems/918512c2-f2e7-4b1c-90e9-a92e3fe66fc1
-- title:
--   Measurable countable supremum functional for right-continuous bounded signed paths
-- statement:
--   Measurable countable supremum functional for right-continuous bounded signed paths
-- source:
--   Kyprianou (2006), Exercise 3.2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectedDenseSupFunctionalV1
    (c : ℝ) (t : NNReal) :
    ∃ H : (NNReal → ℝ) → ℝ, Measurable H ∧
      ∀ g : NNReal → ℝ,
        (∀ u, ContinuousWithinAt g (Ici u) u) →
        BddAbove ((fun u => c * g u) '' Icc 0 t) →
        H g = LevyExtrema.SBA.runSup (fun u => c * g u) t := by
  sorry
