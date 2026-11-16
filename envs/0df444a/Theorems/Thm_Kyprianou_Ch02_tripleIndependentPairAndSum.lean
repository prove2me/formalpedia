-- Prove2me | Theorems.Thm_Kyprianou_Ch02_tripleIndependentPairAndSum
-- name    : Kyprianou.Ch02.tripleIndependentPairAndSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:42:53.190705+00:00
-- url     : https://prove2.me/theorems/957762de-111e-496c-a415-64d269c55ee1
-- title:
--   Triple full-path independence implies pairwise independence and independence of the pair sum from the third path
-- statement:
--   Triple full-path independence implies pairwise independence and independence of the pair sum from the third path. Retain the original triple process independence without adding new assumptions.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, and Prove2Me Chapter 1 independentLevySum proof

import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem tripleIndependentPairAndSum
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω)
      (fun ω => fun t : ℝ≥0 => Xlarge t ω) P ∧
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t : ℝ≥0 => Xsmall t ω) P := by sorry

end Kyprianou.Ch02
