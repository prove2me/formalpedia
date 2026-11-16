-- Prove2me | Theorems.Thm_Kyprianou_Ch02_tripleIndependentPairSumThird
-- name    : Kyprianou.Ch02.tripleIndependentPairSumThird
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:46:52.025244+00:00
-- url     : https://prove2.me/theorems/7234eec8-da9f-4d65-9779-95b182a7bece
-- title:
--   The sum of two members of a fully independent triple is independent of the third entire path
-- statement:
--   The sum of two members of a fully independent triple is independent of the third entire path. Full-path independence is the only stochastic hypothesis.
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

theorem tripleIndependentPairSumThird
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t : ℝ≥0 => Xsmall t ω) P := by sorry

end Kyprianou.Ch02
