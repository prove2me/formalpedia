-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteSmallBandCompensatedExponentAlgebraCh02V1
-- name    : Kyprianou.Ch02.finiteSmallBandCompensatedExponentAlgebraCh02V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:23:33.523661+00:00
-- url     : https://prove2.me/theorems/b3bc8735-7581-4715-8abe-dbdd5605b23c
-- title:
--   Finite bounded small-mark region: combine raw Poisson exponent with deterministic compensation
-- statement:
--   Finite bounded small-mark region: combine raw Poisson exponent with deterministic compensation
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

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
theorem finiteSmallBandCompensatedExponentAlgebraCh02V1
    (ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hfin : ν B < ⊤) (hsmall : ∀ x ∈ B, |x| < 1)
    (t ξ : ℝ) :
    Complex.exp (((-(t * ∫ x in B, x ∂ν) * ξ : ℝ) : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * ∫ x in B,
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) =
      Complex.exp ((t : ℂ) * ∫ x in B,
        ProbabilityTheory.levyCompensatedIntegrand ξ x ∂ν) := by sorry
end Kyprianou.Ch02
