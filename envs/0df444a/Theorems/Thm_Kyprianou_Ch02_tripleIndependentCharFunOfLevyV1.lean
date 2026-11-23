-- Prove2me | Theorems.Thm_Kyprianou_Ch02_tripleIndependentCharFunOfLevyV1
-- name    : Kyprianou.Ch02.tripleIndependentCharFunOfLevyV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:13:29.130148+00:00
-- url     : https://prove2.me/theorems/9b8427df-f5f9-4b02-8317-88d078ae00da
-- title:
--   Theorem 2.1: characteristic function factorisation for independent actual Lévy components
-- statement:
--   For three jointly independent full-path Lévy processes on the same probability space, prove at each time and Fourier parameter that the characteristic function of their sum equals the product of the three component characteristic functions. Fixed-time a.e. measurability is derived from the actual IsLevyProcess hypotheses, avoiding the missing measurability assumptions of the more general tripleIndependentCharFun theorem. Use the pinned iIndepFun.comp evaluation lemma, iIndepFun.charFun_map_sum_eq_prod over Fin 3, and finite-index sum/product simplifications. This is directly applicable to the source-faithful Kyprianou Theorem 2.1 components.
-- source:
--   Kyprianou 2006 Theorem 2.1 characteristic exponent factorisation using whole-path Lévy process independence

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem tripleIndependentCharFunOfLevyV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ProbabilityTheory.IsLevyProcess Xgauss P)
    (hlarge : ProbabilityTheory.IsLevyProcess Xlarge P)
    (hsmall : ProbabilityTheory.IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ := by sorry

end Kyprianou.Ch02
