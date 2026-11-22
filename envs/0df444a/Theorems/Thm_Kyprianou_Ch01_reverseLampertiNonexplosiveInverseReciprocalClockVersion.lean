-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInverseReciprocalClockVersion
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveInverseReciprocalClockVersion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:53:57.704816+00:00
-- url     : https://prove2.me/theorems/f852e790-8678-45eb-9775-7f5af1318dd3
-- title:
--   All-time measurable representative for the reciprocal-occupation right-inverse clock
-- statement:
--   Construct a sectionwise measurable right-inverse of the exact ENNReal reciprocal occupation integral, with all levels agreeing simultaneously with source inverseReciprocalOccupation on one Q-conull event. Use the already established jointly measurable integer compound-Poisson modification to make each nonnegative reciprocal integrand jointly measurable, the pinned Mathlib Measurable.lintegral_prod_right to make each fixed physical-time reciprocal occupation integral measurable, the already Proved monotonicity of reciprocalOccupation, and rational approximation to strict upper passage for the inverse. Rational infima are measurable as countable infima; monotonicity ensures their equality to the original right-inverse for all levels on the common good event. The explicit non-explosion hypothesis ensures eventual finite upper-passage witnesses; do not assume finite offspring expectation or continuity of the extended-valued clock.
-- source:
--   Kyprianou 2006 §1.3.4 reverse Lamperti, existing root ac1b29c6-5525-4344-a03d-7469824736ed and child efffa70f-388d-47f5-aaf1-bd6b06171153. Exact source inverseReciprocalOccupation from Def_Kyprianou_Ch01_LampertiInverse. Reuse Proved reciprocalOccupationMonotone d401e83a-e957-4235-98fe-1c200c964b6e, new root-connected joint integer version 16c022df-d006-4521-8a26-2c3b085468b6, and pinned Mathlib Measurable.lintegral_prod_right (exact type verified with remote signature probe).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveInverseReciprocalClockVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    ∀ y : ℕ, ∃ U : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (U t)) ∧
      ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
        U t ω = inverseReciprocalOccupation
          (integerCompoundPoisson y arrival marks) t ω := by
  sorry
