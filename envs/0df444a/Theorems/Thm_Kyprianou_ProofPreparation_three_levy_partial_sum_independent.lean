-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_three_levy_partial_sum_independent
-- name    : Kyprianou.ProofPreparation.three_levy_partial_sum_independent
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T22:59:59.362174+00:00
-- url     : https://prove2.me/theorems/3b32f561-6298-433e-8282-005d29ca2a41
-- title:
--   Whole-path independence of a partial two-component Lévy sum and its third driver
-- statement:
--   Whole-path mutual independence of three Lévy-Ito drivers implies independence of the pointwise path sum of the first two from the third driver. This preserves the path-level, rather than merely fixed-time, independence requirement.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.1, pp. 35–36 and proof pp. 50–53.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem three_levy_partial_sum_independent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    IndepFun
      (fun ω => fun t => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t => Xsmall t ω) P := by sorry
end Kyprianou.ProofPreparation
