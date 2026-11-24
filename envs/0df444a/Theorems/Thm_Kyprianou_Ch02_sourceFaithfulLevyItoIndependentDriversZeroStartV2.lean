-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoIndependentDriversZeroStartV2
-- name    : Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversZeroStartV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:30:40.260861+00:00
-- url     : https://prove2.me/theorems/d91ba02d-8193-47cf-9748-e64bd616787e
-- title:
--   Construct independent Brownian and PRM drivers with pathwise-zero Brownian origin
-- statement:
--   Construct independent Brownian and Poisson random measure drivers on one product probability space and ensure the Brownian path W(0,ω)=0 at every sample point. The original BrownianMotion record only guarantees W(0)=0 P-almost surely, and the unrestricted driver-to-Lévy components theorem was formally Disproved on 23 November 2026 by an exceptional-path counterexample. Normalise W by subtracting W(0) pointwise, verify the unchanged increment laws, the measurable path structure and the past-future independence, and transport independence from the Poisson driver. The resulting stronger existential witness is genuine and supplies the missing pathwise hypothesis to source-faithful components.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1; independent driving Brownian motion normalised at time zero.

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

theorem sourceFaithfulLevyItoIndependentDriversZeroStartV2
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
          (∀ ω : Ω, B.W 0 ω = 0) ∧
          ProbabilityTheory.IndepFun
            (fun ω => fun (t : ℝ) => B.W t ω)
            (fun ω => N.N ω) P := by sorry

end Kyprianou.Ch02
