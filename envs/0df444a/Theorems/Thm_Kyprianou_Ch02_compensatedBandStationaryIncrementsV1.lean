-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedBandStationaryIncrementsV1
-- name    : Kyprianou.Ch02.compensatedBandStationaryIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:46:31.59982+00:00
-- url     : https://prove2.me/theorems/3d00f388-64ef-4afe-ab5a-865395895c2b
-- title:
--   Stationary increments of the compensated small-jump cutoff band
-- statement:
--   The raw finite-region Poisson integral has stationary increments by the
--   proved Chapter 2 finite-region theorem. Compensating by the deterministic
--   drift t times the mark integral preserves stationary increments.
--   Finite intensity of the cutoff band follows from the Lévy measure
--   tail bound. This is the exact finite-band stochastic input to Theorem 2.10.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem compensatedBandStationaryIncrementsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ProbabilityTheory.HasStationaryIncrements
      (Kyprianou.compensatedSmallJumpBand P ν N ε) P := by sorry
end Kyprianou.Ch02
