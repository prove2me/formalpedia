-- Prove2me | Theorems.Thm_Kyprianou_largeJumpProcessLevy
-- name    : Kyprianou.largeJumpProcessLevy
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T11:13:36.385668+00:00
-- url     : https://prove2.me/theorems/5c06d985-05f1-4c04-aa68-fc6de328bbfa
-- title:
--   Eq. (2.3): finite-activity large-jump Lévy component
-- statement:
--   The large jumps |x|>=1 form a compound Poisson Lévy process with finite rate, including the zero-intensity case.
-- source:
--   Kyprianou (2006), Eq. (2.3), p. 34; Lemma 2.8, pp. 44–45

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
theorem largeJumpProcessLevy
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ProbabilityTheory.IsLevyProcess (largeJumpProcess P levyMeasure N) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (largeJumpProcess P levyMeasure N t)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in {x : ℝ | 1 ≤ |x|},
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure)
      := by sorry
end Kyprianou
