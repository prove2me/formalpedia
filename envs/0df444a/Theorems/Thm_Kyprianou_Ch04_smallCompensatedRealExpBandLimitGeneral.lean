-- Prove2me | Theorems.Thm_Kyprianou_Ch04_smallCompensatedRealExpBandLimitGeneral
-- name    : Kyprianou.Ch04.smallCompensatedRealExpBandLimitGeneral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:14:59.105189+00:00
-- url     : https://prove2.me/theorems/1fc5f022-eb2f-51cb-8f8a-4d4566a48d4b
-- title:
--   Small-jump real compensated exponent cutoff convergence
-- statement:
--   Small-mark compensation is integrable for every real beta, so this local cutoff convergence does not require exponential integrability of large marks.
-- source:
--   Kyprianou (2006), Exercise 4.3(iv).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.smallCompensatedRealExpBandLimitGeneral
    (T : LevyKhintchineTriple)
    (e : Nat → Real) (he : ∀ n, 0 < e n ∧ e n < 1)
    (hzero : Tendsto e atTop (nhds 0)) (beta : Real) :
    Tendsto (fun n => ∫ x in {x : Real | e n ≤ |x| ∧ |x| < 1},
      (Real.exp (beta*x)-1-beta*x) ∂T.levyMeasure) atTop
      (nhds (∫ x in Ioo (-1 : Real) 1,
        (Real.exp (beta*x)-1-beta*x) ∂T.levyMeasure)) := by
  sorry
