-- Prove2me | Theorems.Thm_Kyprianou_sumOfIndependentLevyProcesses
-- name    : Kyprianou.sumOfIndependentLevyProcesses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:29:21.016311+00:00
-- url     : https://prove2.me/theorems/75b7bc4b-bf1c-4804-b526-b8e715b0a6c8
-- title:
--   Sum of independent Lévy processes and characteristic-function factorisation
-- statement:
--   Mutually independent Lévy processes have a Lévy sum and its marginal characteristic functions factorise.
-- source:
--   Kyprianou (2006), proof of Theorem 2.1, pp. 51–53

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

namespace Kyprianou
theorem sumOfIndependentLevyProcesses
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ProbabilityTheory.IsLevyProcess Xgauss P)
    (hlarge : ProbabilityTheory.IsLevyProcess Xlarge P)
    (hsmall : ProbabilityTheory.IsLevyProcess Xsmall P)
    (hind : IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => Xgauss t ω + Xlarge t ω + Xsmall t ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ
      := by sorry
end Kyprianou
