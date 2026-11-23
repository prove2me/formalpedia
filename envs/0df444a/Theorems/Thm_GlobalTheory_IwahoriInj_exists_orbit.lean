-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_exists_orbit
-- name    : GlobalTheory.IwahoriInj.exists_orbit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:55.602802+00:00
-- url     : https://prove2.me/theorems/d82c33d6-f8bc-4047-8c01-2962c5f15a23
-- title:
--   Iwahori Inj: exists orbit
-- statement:
--   The Iwahori Inj construction uses the exists orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L45-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.IwahoriInj.exists_orbit (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) (v : V) :
    ∃ S : Finset V, (∀ u, u ∈ S ↔ ∃ h ∈ H, π h v = u) ∧ ∑ u ∈ S, u ∈ fixed π H := by sorry
