-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoIndependentDriversV1
-- name    : Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:45:20.957834+00:00
-- url     : https://prove2.me/theorems/8649e2dc-75b0-4563-ae5f-39d894a26849
-- title:
--   Theorem 2.1: construct independent Brownian and Poisson random-measure drivers on one product probability space
-- statement:
--   For an arbitrary sigma-finite Levy measure, construct a genuine common probability space with an entire Brownian motion and a Poisson random measure, and establish independence of their full random paths and full measure-valued random variables. The construction must preserve both source structures, not merely marginal laws or fixed-time independence. The direct approach is the product of the existing pinned Brownian existence witness and the PRM existence witness, lifted via the measure product.
-- source:
--   Kyprianou 2006 Theorem 2.1 independent Gaussian and PRM driving noises

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

theorem sourceFaithfulLevyItoIndependentDriversV1
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
          ProbabilityTheory.IndepFun
            (fun ω => fun (t : ℝ) => B.W t ω)
            (fun ω => N.N ω) P := by sorry

end Kyprianou.Ch02
