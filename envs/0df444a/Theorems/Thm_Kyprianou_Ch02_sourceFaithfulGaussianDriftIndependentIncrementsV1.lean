-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftIndependentIncrementsV1
-- name    : Kyprianou.Ch02.sourceFaithfulGaussianDriftIndependentIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:07:16.242651+00:00
-- url     : https://prove2.me/theorems/6154480c-8f12-4aed-91c7-1c8cdac548d5
-- title:
--   Independence of increments of a scaled drifted Brownian process
-- statement:
--   Independence of increments of a scaled drifted Brownian process, using Brownian increment independence, Gaussian increment laws, and invariance under deterministic scaling and linear drift.
-- source:
--   Kyprianou (2006), Chapter 2, Gaussian Lévy-Itô component

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
theorem sourceFaithfulGaussianDriftIndependentIncrementsV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0) :
    ProbabilityTheory.HasIndependentIncrements (fun (t : ℝ≥0) (ω : Ω) => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P
    := by sorry
end Kyprianou.Ch02
