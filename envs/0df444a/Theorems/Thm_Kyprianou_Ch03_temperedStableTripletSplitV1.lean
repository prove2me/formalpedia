-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableTripletSplitV1
-- name    : Kyprianou.Ch03.temperedStableTripletSplitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:49:45.753905+00:00
-- url     : https://prove2.me/theorems/1e161022-b685-451c-a602-4bfc50917287
-- title:
--   Split a signed tempered stable triplet into two positive-jump triplets
-- statement:
--   The two summands of the signed jump measure inherit Lévy integrability; undo reflection for the negative summand. Assign the original drift to TP and zero to TM, and split the compensated integral.
-- source:
--   Kyprianou (2006), Exercise 3.4, auxiliary obligations for temperedStableDecomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableTripletSplitV1
    (T : LevyKhintchineTriple)
    (cp ap gp cm am gm : ℝ) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      Kyprianou.Ch03.temperedStableSignedMeasure cp ap gp cm am gm) :
    ∃ TP TM : LevyKhintchineTriple,
      TP.gaussianVariance = 0 ∧ TM.gaussianVariance = 0 ∧
      TP.levyMeasure = Kyprianou.Ch03.temperedStablePositiveMeasure cp ap gp ∧
      TM.levyMeasure = Kyprianou.Ch03.temperedStablePositiveMeasure cm am gm ∧
      ∀ xi, Kyprianou.Ch01.levyTripleExponent T xi =
        Kyprianou.Ch01.levyTripleExponent TP xi +
        Kyprianou.Ch01.levyTripleExponent TM (-xi) := by sorry
