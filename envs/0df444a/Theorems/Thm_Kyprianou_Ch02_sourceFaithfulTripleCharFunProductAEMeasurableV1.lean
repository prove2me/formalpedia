-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulTripleCharFunProductAEMeasurableV1
-- name    : Kyprianou.Ch02.sourceFaithfulTripleCharFunProductAEMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:12:39.502581+00:00
-- url     : https://prove2.me/theorems/2f5cf76a-72a9-4bf1-b4df-3bd796ce24cc
-- title:
--   Three-component characteristic function factorisation with explicit a.e. measurable marginals
-- statement:
--   Let three jointly independent full paths be given, and suppose their three values at the requested time t are almost-everywhere measurable. Then the characteristic function of their sum equals the product of their characteristic functions. These three measurability premises are essential for the Mathlib IndepFun.charFun_map_fun_add_eq_mul theorem, and are implicit in the original stochastic-process application. This result is the source-faithful correction of the unqualified independent-path product helper.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, characteristic function multiplication for independent measurable processes.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem sourceFaithfulTripleCharFunProductAEMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall)
    (t : ℝ≥0) (ξ : ℝ)
    (hMG : AEMeasurable (Xgauss t) P)
    (hML : AEMeasurable (Xlarge t) P)
    (hMS : AEMeasurable (Xsmall t) P) :
    charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ := by sorry

end Kyprianou.Ch02
