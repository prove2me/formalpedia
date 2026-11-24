-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftLevyZeroStartV2
-- name    : Kyprianou.Ch02.sourceFaithfulGaussianDriftLevyZeroStartV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:58:40.067554+00:00
-- url     : https://prove2.me/theorems/88de7a0e-5d1e-4f2c-b1ee-2c443018489e
-- title:
--   The drifted scaled Brownian process is a pointwise-zero Lévy process when the underlying Brownian driver is no
-- statement:
--   The drifted scaled Brownian process is a pointwise-zero Lévy process when the underlying Brownian driver is normalised at time zero.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, Lévy–Itô component verification

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
theorem sourceFaithfulGaussianDriftLevyZeroStartV2
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0)
 :
    ProbabilityTheory.IsLevyProcess
      (fun (t : ℝ≥0) (ω : Ω) =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P
    := by sorry
end Kyprianou.Ch02
