-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_map_comp_integrated
-- name    : GroundTheory.Automorphic.UnitaryRep.map_comp_integrated
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:18.105247+00:00
-- url     : https://prove2.me/theorems/f52d3026-d189-4e9a-b0e3-138f732d9822
-- title:
--   Unitary Rep: map comp integrated
-- statement:
--   The Unitary Rep construction uses the map comp integrated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L182-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L182-L190

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

theorem GroundTheory.Automorphic.UnitaryRep.map_comp_integrated [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) :
    π h ∘L π.integrated μ f = π.integrated μ (leftTranslate μ h f) := by sorry
