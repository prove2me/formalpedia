-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_levy_three_sum_of_partial_independence
-- name    : Kyprianou.ProofPreparation.levy_three_sum_of_partial_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:59:57.659025+00:00
-- url     : https://prove2.me/theorems/7aafe58e-4fe7-439a-ada9-ce784781e0a1
-- title:
--   Three-component Lévy process closure from partial-sum path independence
-- statement:
--   Once whole-path independence between a two-component Levy sum and the third Levy driver is known, apply Chapter 1 independent Levy-process addition twice to obtain the full three-component sum as a Levy process.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.1, pp. 35–36 and proof pp. 50–53.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem levy_three_sum_of_partial_independence
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall)
    (hpairThird : IndepFun
      (fun ω => fun t => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t => Xsmall t ω) P) :
    IsLevyProcess (fun t ω =>
      Xgauss t ω + Xlarge t ω + Xsmall t ω) P := by sorry
end Kyprianou.ProofPreparation
