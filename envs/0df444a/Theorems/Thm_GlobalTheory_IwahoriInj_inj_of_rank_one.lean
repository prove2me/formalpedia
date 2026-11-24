-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_inj_of_rank_one
-- name    : GlobalTheory.IwahoriInj.inj_of_rank_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:22:24.821472+00:00
-- url     : https://prove2.me/theorems/bb55602a-8fc2-424b-a41a-a61447e7ac5b
-- title:
--   Iwahori Inj: inj of rank one
-- statement:
--   The Iwahori Inj construction uses the inj of rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L82-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L82-L108

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

theorem GlobalTheory.IwahoriInj.inj_of_rank_one (hπ : IsSmooth π) {I J P : Subgroup G} (hJ : IsCompact (J : Set G))
    (hP : IsCompact (P : Set G)) (hJP : J ≤ P) {s : G} (hs : s ∈ P) (hconj : ∀ x ∈ J, s⁻¹ * x * s ∈ I)
    (hdec : ∀ p ∈ P, (∃ a ∈ J, ∃ b ∈ I, p = a * b) ∨ s⁻¹ * p ∈ I) : Inj π I J := by sorry
