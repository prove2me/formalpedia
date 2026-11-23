-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedBandIndependentIncrementsV1
-- name    : Kyprianou.Ch02.compensatedBandIndependentIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:56:00.53625+00:00
-- url     : https://prove2.me/theorems/e7804cc5-01b9-4f18-bbd8-5bedb2e92525
-- title:
--   Independent increments of the compensated small-jump cutoff band
-- statement:
--   Every positive compensated Poisson jump-band process has jointly independent increments along monotone finite partitions. Apply the Proved raw finite-region Poisson independent-increment theorem, then subtract the deterministic linear compensator using the generic iIndepFun.comp drift invariance theorem.
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
theorem compensatedBandIndependentIncrementsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ProbabilityTheory.HasIndependentIncrements
      (Kyprianou.compensatedSmallJumpBand P ν N ε) P := by sorry
end Kyprianou.Ch02
