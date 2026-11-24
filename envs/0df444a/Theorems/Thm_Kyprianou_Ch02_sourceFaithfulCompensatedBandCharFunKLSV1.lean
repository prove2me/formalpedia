-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulCompensatedBandCharFunKLSV1
-- name    : Kyprianou.Ch02.sourceFaithfulCompensatedBandCharFunKLSV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:15:13.183309+00:00
-- url     : https://prove2.me/theorems/8f21f04b-5060-45a1-9196-42386f7e56a2
-- title:
--   Characteristic function of a finite compensated KLS Poisson band
-- statement:
--   Use the proved finiteRegionPoissonIntegralCh02V3 on the finite separated band and translate by its deterministic compensator.
-- source:
--   Kyprianou (2006), Chapter 2, proof of Theorem 2.1, compensated small-jump characteristic exponent

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
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
theorem sourceFaithfulCompensatedBandCharFunKLSV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (Kyprianou.compensatedSmallJumpBand P levyMeasure N e t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | e ≤ |x| ∧ |x| < 1},
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) := by sorry
end Kyprianou.Ch02
