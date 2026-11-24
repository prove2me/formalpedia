-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_source_exit_clocks_eq
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_source_exit_clocks_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T04:25:42.704454+00:00
-- url     : https://prove2.me/theorems/d23115b6-e9f4-4e5b-9262-acbaf278d1d0
-- title:
--   Source exit clocks transfer to the filtered Avram model
-- statement:
--   Almost-sure path equality identifies the source upper and lower passage clocks with the corresponding filtered Avram clocks, including the lower clock of the process started at the upper barrier.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_source_exit_clocks_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω) (x a : ℝ) :
    ∀ᵐ ω ∂P,
      tauPlus (shifted D.X x) a ω = twoSidedExitUpTime X (a - x) ω ∧
      tauMinus (shifted D.X x) 0 ω = twoSidedExitDownTime X (-x) ω ∧
      tauMinus (shifted D.X a) 0 ω = tauMinus (shifted X.X a) 0 ω
:= by
  sorry
