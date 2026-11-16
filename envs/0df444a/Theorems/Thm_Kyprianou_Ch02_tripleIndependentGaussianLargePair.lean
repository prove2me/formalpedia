-- Prove2me | Theorems.Thm_Kyprianou_Ch02_tripleIndependentGaussianLargePair
-- name    : Kyprianou.Ch02.tripleIndependentGaussianLargePair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:48:35.081077+00:00
-- url     : https://prove2.me/theorems/aac29c11-9cca-4eaf-ac84-f0a11856c992
-- title:
--   Triple full-path independence implies independence of the first two paths
-- statement:
--   Triple full-path independence implies independence of the first two paths. Direct two-index projection of a fully independent triple.
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

theorem tripleIndependentGaussianLargePair
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ProbabilityTheory.IndepFun
      (fun ω => fun t : ℝ≥0 => Xgauss t ω)
      (fun ω => fun t : ℝ≥0 => Xlarge t ω) P := by sorry

end Kyprianou.Ch02
