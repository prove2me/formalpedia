-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_norm_integrated_apply_le
-- name    : GroundTheory.Automorphic.UnitaryRep.norm_integrated_apply_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:23.604587+00:00
-- url     : https://prove2.me/theorems/d4aa4a83-0646-4cc8-bebf-f80ca47ec8af
-- title:
--   Unitary Rep: norm integrated apply le
-- statement:
--   The Unitary Rep construction uses the norm integrated apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L107-L109

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

theorem GroundTheory.Automorphic.UnitaryRep.norm_integrated_apply_le (f : G →₁[μ] ℂ) (v : H) :
    ‖π.integrated μ f v‖ ≤ ‖f‖ * ‖v‖ := by sorry
