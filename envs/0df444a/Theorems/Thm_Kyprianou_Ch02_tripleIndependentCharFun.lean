-- Prove2me | Theorems.Thm_Kyprianou_Ch02_tripleIndependentCharFun
-- name    : Kyprianou.Ch02.tripleIndependentCharFun
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:42:57.029319+00:00
-- url     : https://prove2.me/theorems/9676115f-8b84-465b-874f-efe8418a2fc3
-- title:
--   Characteristic function of three independent entire paths factorises at every time
-- statement:
--   Characteristic function of three independent entire paths factorises at every time. Retain the original triple process independence without adding new assumptions.
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

theorem tripleIndependentCharFun
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      charFun (P.map (Xgauss t)) ξ *
      charFun (P.map (Xlarge t)) ξ *
      charFun (P.map (Xsmall t)) ξ := by sorry

end Kyprianou.Ch02
