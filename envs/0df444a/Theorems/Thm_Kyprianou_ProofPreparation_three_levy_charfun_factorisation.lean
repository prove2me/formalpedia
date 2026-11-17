-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_three_levy_charfun_factorisation
-- name    : Kyprianou.ProofPreparation.three_levy_charfun_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:54:23.748382+00:00
-- url     : https://prove2.me/theorems/25522437-32fd-4ec8-9809-3888be500fa2
-- title:
--   Characteristic-function factorisation for three mutually independent Lévy processes
-- statement:
--   For three mutually whole-path independent real Levy processes, the characteristic function of their pointwise sum at any nonnegative time and real frequency equals the product of their marginal characteristic functions. The independence assumption is the exact Chapter 2 three-component definition.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.1 construction, pp. 35–36 and pp. 50–53.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem three_levy_charfun_factorisation
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents
      P Xgauss Xlarge Xsmall)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      charFun (P.map (Xgauss t)) ξ *
      charFun (P.map (Xlarge t)) ξ *
      charFun (P.map (Xsmall t)) ξ := by sorry
end Kyprianou.ProofPreparation
