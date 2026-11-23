-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
-- name    : GlobalTheory.IwahoriInj.Inj.trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:03.451889+00:00
-- url     : https://prove2.me/theorems/b6b7c58b-0b43-4c41-8d9a-59e143c9c6e7
-- title:
--   Inj: trans
-- statement:
--   The Inj construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L65-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L65-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

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

theorem GlobalTheory.IwahoriInj.Inj.trans (hπ : IsSmooth π) {I J K : Subgroup G} (hJ : IsCompact (J : Set G))
    (hfac : ∀ x ∈ J, ∃ a ∈ K, ∃ b ∈ I, x = a * b) (h1 : Inj π I J) (h2 : Inj π J K) : Inj π I K := by sorry
