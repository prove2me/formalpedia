-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_extendZero_apply_coe
-- name    : GroundTheory.Automorphic.UnitaryRep.extendZero_apply_coe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:52.113157+00:00
-- url     : https://prove2.me/theorems/71155857-5c16-48db-adcd-c70c77cc7a19
-- title:
--   Unitary Rep: extend Zero apply coe
-- statement:
--   The Unitary Rep construction uses the extend Zero apply coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L57-L60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology Function
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
set_option linter.unusedSectionVars false
variable [IsTopologicalGroup G] [T2Space G]
open Classical

theorem GroundTheory.Automorphic.UnitaryRep.extendZero_apply_coe {L : Subgroup G} (hL : IsOpen (L : Set G))
    (f : CompactlySupportedContinuousMap L ℂ) (x : L) : extendZero hL f x = f x := by sorry
