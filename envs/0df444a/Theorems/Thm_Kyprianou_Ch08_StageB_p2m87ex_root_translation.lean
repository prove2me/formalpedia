-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87ex_root_translation
-- name    : Kyprianou.Ch08.StageB.p2m87ex_root_translation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:30:38.65229+00:00
-- url     : https://prove2.me/theorems/38ee68f6-7035-4971-87ab-357abe751c54
-- title:
--   Largest tilted root translates to largest original root
-- statement:
--   The translated root belongs to the original nonnegative root set; every original root below c is smaller, and every original root above c corresponds to a tilted root.
-- source:
--   Kyprianou (2006), Exercise 8.7(i); decomposition of af7546b2-54be-4df1-896f-3b885337ff41.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m87ex_root_translation
    (ψ : ℝ → ℝ) (c q : ℝ) (hc : 0 ≤ c)
    (hr : PhiIsLargestRoot (shiftedExponent ψ c) q) :
    Phi (shiftedExponent ψ c) q = Phi ψ (q + ψ c) - c := by
  sorry
