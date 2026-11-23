-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_integrated_of_mem_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.comp_integrated_of_mem_intertwiners
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:09.857489+00:00
-- url     : https://prove2.me/theorems/bdc99626-37a1-436d-b3f6-a72ba22d3ba1
-- title:
--   Unitary Rep: comp integrated of mem intertwiners
-- statement:
--   The Unitary Rep construction uses the comp integrated of mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L144-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L144-L150

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

theorem GroundTheory.Automorphic.UnitaryRep.comp_integrated_of_mem_intertwiners {σ : UnitaryRep G K} {T : H →L[ℂ] K}
    (hT : T ∈ π.intertwiners σ) (f : G →₁[μ] ℂ) :
    T ∘L π.integrated μ f = σ.integrated μ f ∘L T := by sorry
