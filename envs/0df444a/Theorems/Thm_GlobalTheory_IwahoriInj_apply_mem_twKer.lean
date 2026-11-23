-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_apply_mem_twKer
-- name    : GlobalTheory.IwahoriInj.apply_mem_twKer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:35.879182+00:00
-- url     : https://prove2.me/theorems/7f0ade13-3762-441e-a0d7-2803ed499074
-- title:
--   Iwahori Inj: apply mem tw Ker
-- statement:
--   The Iwahori Inj construction uses the apply mem tw Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L27-L29

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

theorem GlobalTheory.IwahoriInj.apply_mem_twKer {H : Subgroup G} {h : G} (hh : h ∈ H) {v : V} (hv : v ∈ twKer π H 1) :
    π h v ∈ twKer π H 1 := by sorry
