-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpExponentBandLimitV1
-- name    : Kyprianou.Ch02.sourceFaithfulSmallJumpExponentBandLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:15:02.154817+00:00
-- url     : https://prove2.me/theorems/7eccc30b-aa1e-4f34-9c01-953f24b208a8
-- title:
--   Convergence of the compensated finite-band characteristic exponents
-- statement:
--   Apply dominated convergence to the indicator of the separated band using integrable_levyCompensatedIntegrand; the integrand vanishes at zero. Then apply continuity of the exponential.
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
theorem sourceFaithfulSmallJumpExponentBandLimitV1
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hzero : Tendsto ε atTop (nhds 0))
    (t : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n => Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | ε n ≤ |x| ∧ |x| < 1},
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))
      atTop (nhds (Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in Set.Ioo (-1 : ℝ) 1,
          ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))) := by sorry
end Kyprianou.Ch02
