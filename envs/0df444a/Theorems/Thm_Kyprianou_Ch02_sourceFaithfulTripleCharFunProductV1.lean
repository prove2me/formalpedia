-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulTripleCharFunProductV1
-- name    : Kyprianou.Ch02.sourceFaithfulTripleCharFunProductV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:56:58.270305+00:00
-- url     : https://prove2.me/theorems/a0037416-5ee0-497d-b4c2-694734321e84
-- title:
--   Characteristic-function factorisation of mutually independent Lévy–Itô component paths
-- statement:
--   Independence of the three full Lévy–Itô component paths implies their time-t marginals are mutually independent and their joint sum has characteristic function equal to the product of the three marginal characteristic functions. The hind hypothesis alone suffices: the earlier source theorem three_levy_charfun_factorisation unnecessarily required each component to satisfy IsLevyProcess. Recover independence by measurable time evaluation and use Mathlib charFun add for independent real functions.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1: characteristic exponent of the three Lévy–Itô components.

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

theorem sourceFaithfulTripleCharFunProductV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ := by sorry

end Kyprianou.Ch02
