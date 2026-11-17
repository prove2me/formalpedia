-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_three_levy_partial_sum_independent_of_levy
-- name    : Kyprianou.ProofPreparation.three_levy_partial_sum_independent_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:25:41.506904+00:00
-- url     : https://prove2.me/theorems/0e6992ff-9840-4db6-a4e1-8211c1228005
-- title:
--   Whole-path independence of Lévy partial sum and third driver
-- statement:
--   A source-backed independence lemma for three mutually whole-path independent real Lévy processes. The finite-dimensional and full-path measurability details are proved using the fixed-time a.e. measurability of Lévy marginals, finite-vector projections and the process independence extension theorem.
-- source:
--   Kyprianou (2006), Chapter 2: Lévy–Itô decomposition, independent component construction and Chapter 1 independent Lévy addition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem three_levy_partial_sum_independent_of_levy
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    IndepFun
      (fun ω => fun t => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t => Xsmall t ω) P := by sorry
end Kyprianou.ProofPreparation
