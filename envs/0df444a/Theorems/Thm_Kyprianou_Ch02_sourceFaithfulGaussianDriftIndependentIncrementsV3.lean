-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftIndependentIncrementsV3
-- name    : Kyprianou.Ch02.sourceFaithfulGaussianDriftIndependentIncrementsV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:08:56.777766+00:00
-- url     : https://prove2.me/theorems/bc6ea59c-d44b-456d-b79d-21c00a921abe
-- title:
--   Apply the proved KLS Brownian finite partition independence bridge, then apply the deterministic affine transformation to each increment, using the actual lag of its partition interval.
-- statement:
--   Apply the proved KLS Brownian finite partition independence bridge, then apply the deterministic affine transformation to each increment, using the actual lag of its partition interval.
-- source:
--   Kyprianou (2006), Theorem 2.1, Gaussian component.

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
theorem sourceFaithfulGaussianDriftIndependentIncrementsV3
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P := by sorry
end Kyprianou.Ch02
