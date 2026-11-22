-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveJointIntegerProcessVersion
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:40:01.830993+00:00
-- url     : https://prove2.me/theorems/16c022df-d006-4521-8a26-2c3b085468b6
-- title:
--   Jointly measurable integer-valued compound Poisson modification agreeing with all source times on a common conull event
-- statement:
--   Construct a jointly measurable integer-valued process W agreeing with integerCompoundPoisson y arrival marks s ω at every NNReal time s on a single Q-conull event. The source fixed-time measurability and a.e. right continuity are already Proved, as are the driver arrival measurability properties and the generic real-valued jointly measurable right-continuous process theorem. Select a measurable conull event G where all-time right continuity holds. Gate the source X to zero off G, cast to real, apply the proved rightContinuous_measurable_sections_joint_evaluation and recover the integer-valued W using Int.floor (which is exact for integer inputs). This provides all-time, rather than separately fixed-time, equality. No finite offspring moment is assumed.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4 reverse Lamperti law, root theorem ac1b29c6-5525-4344-a03d-7469824736ed, connected witness parent 4c40c848-86b4-4c33-8f82-4106ca9fe438, mission 9919725d-217e-48cb-9cd1-bb779a69b820; pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Reuse Proved integerCompoundPoissonFixedTimeMeasurable 4a215c58-846c-47b2-990a-fad256013ece, integerCompoundPoissonRightContinuousAE 89e2d356-663a-425c-afcd-ad3841267c58, and rightContinuous_measurable_sections_joint_evaluation 8aafec11-d8a5-443c-9386-270a0d5c8a04.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ, ∃ W : ℝ≥0 → Ω → ℤ,
      Measurable (fun z : ℝ≥0 × Ω => W z.1 z.2) ∧
      ∀ᵐ ω ∂Q, ∀ s : ℝ≥0,
        W s ω = integerCompoundPoisson y arrival marks s ω := by
  sorry
