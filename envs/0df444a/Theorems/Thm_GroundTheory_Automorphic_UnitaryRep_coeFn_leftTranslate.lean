-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coeFn_leftTranslate
-- name    : GroundTheory.Automorphic.UnitaryRep.coeFn_leftTranslate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:34:08.917728+00:00
-- url     : https://prove2.me/theorems/66864def-bd94-4563-9e51-8850074dcf79
-- title:
--   Unitary Rep: coe Fn left Translate
-- statement:
--   The Unitary Rep construction uses the coe Fn left Translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L178-L180

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
variable [IsTopologicalGroup G] [BorelSpace G]
omit [OpensMeasurableSpace G]

theorem GroundTheory.Automorphic.UnitaryRep.coeFn_leftTranslate [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) :
    (leftTranslate μ h f : G → ℂ) =ᵐ[μ] fun g => f (h⁻¹ * g) := by sorry
