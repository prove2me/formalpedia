-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_toLp_apply
-- name    : GroundTheory.Automorphic.UnitaryRep.integrated_toLp_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:04.445522+00:00
-- url     : https://prove2.me/theorems/b59e5991-e808-4048-a031-7d702725660b
-- title:
--   Unitary Rep: integrated to Lp apply
-- statement:
--   The Unitary Rep construction uses the integrated to Lp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L130-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L130-L142

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)

theorem GroundTheory.Automorphic.UnitaryRep.integrated_toLp_apply [IsFiniteMeasureOnCompacts μ]
    (f : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π.integrated μ ((f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1)
      f.hasCompactSupport).toLp f) v = ∫ g, f g • π g v ∂μ := by sorry
