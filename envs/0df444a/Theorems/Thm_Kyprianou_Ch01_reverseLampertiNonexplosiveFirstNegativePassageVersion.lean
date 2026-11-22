-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveFirstNegativePassageVersion
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveFirstNegativePassageVersion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:54:00.266278+00:00
-- url     : https://prove2.me/theorems/10562bdb-b68f-4aca-a129-b9c618aca569
-- title:
--   Measurable common-event version of the first strict negative lattice passage
-- statement:
--   Construct a globally measurable version of firstNegativePassage for the integer compound-Poisson driver. The initial lattice state is y≥0 almost surely by the existing Proved compoundPoisson_ae_start. The Proved firstNegativePassageEqShiftedFirstNonpositive identifies the strict negative passage with the first nonpositive time of the integer process shifted by +1. This shifted process is right-continuous at all times on an existing common conull event by Proved integerCompoundPoissonRightContinuousAE, and all fixed-time sections are measurable. Apply the Proved firstNonpositiveLatticeEqRationalOfRightContinuous and rationalFirstNonpositiveLatticeClockMeasurable to construct a rational-grid measurable clock. On the common conull event the rational clock equals the original passage. The result can also be obtained using the original shifted firstNonpositiveLatticeAEMeasurableFromDriver after proving the exact integer initial-shift identity; either source-faithful route is valid.
-- source:
--   Kyprianou 2006 §1.3.4, root ac1b29c6-5525-4344-a03d-7469824736ed via stopped clock child efffa70f-388d-47f5-aaf1-bd6b06171153. Proved firstNegativePassageEqShiftedFirstNonpositive 85ccb3e8-54ec-4ae7-ad8c-68d55eb140ef, firstNonpositiveLatticeEqRationalOfRightContinuous 63f8b2f6-625b-42e0-9e2a-c94f66721b02, rationalFirstNonpositiveLatticeClockMeasurable 334ca786-7cbc-43cf-92d2-95adb1216fab, integerCompoundPoissonRightContinuousAE 89e2d356-663a-425c-afcd-ad3841267c58, and compoundPoisson_ae_start 95eb107c-9bdf-4676-87ac-9e5b2fa13526.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveFirstNegativePassageVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ, ∃ V : Ω → WithTop ℝ≥0,
      Measurable V ∧
      ∀ᵐ ω ∂Q, V ω =
        firstNegativePassage (integerCompoundPoisson y arrival marks) ω := by
  sorry
