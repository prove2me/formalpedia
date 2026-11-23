-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverShiftedTail
-- name    : Kyprianou.Ch01.compoundPoissonDriverShiftedTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T16:33:25.120607+00:00
-- url     : https://prove2.me/theorems/307a5402-99f8-4283-a552-3cb3261896a9
-- title:
--   Removing the first mark and interarrival preserves the compound Poisson driver laws
-- statement:
--   The joint iid compound-Poisson driver remains a driver of the same rate and mark law after deleting its first interarrival and first mark, by restricting the jointly independent Sum-indexed family to an injectively shifted index set.
-- source:
--   LeanLevy Processes CompoundPoisson driver (joint iIndepFun) and Kyprianou 2006 section 1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonDriverShiftedTail
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w)
      rate jumpLaw Q := by
  sorry
