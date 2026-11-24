-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallMarkPRMCompactStrictEnvelopeV1
-- name    : Kyprianou.Ch02.smallMarkPRMCompactStrictEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:50:13.687564+00:00
-- url     : https://prove2.me/theorems/980f2b30-2960-4aa6-893f-6e1c0566b2db
-- title:
--   All small marks on a compact time window admit a common strict upper envelope
-- statement:
--   The band with 1/2 ≤ |x| < 1 has finite Lévy measure. Use finite support on a natural window containing T. Filter that finite support to points in the band, and choose the maximum of 1/2 and their absolute marks; this maximum is strictly below one. All marks above that maximum have zero mass.
-- source:
--   Kyprianou (2006), Theorem 2.1. Strict jump-size bound for the compensated small-jump component; child of sourceFaithfulSmallJumpBandsCompactJumpCapV1.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.smallMarkPRMCompactStrictEnvelopeV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (hν : ProbabilityTheory.IsLevyMeasure ν) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0 := by sorry
