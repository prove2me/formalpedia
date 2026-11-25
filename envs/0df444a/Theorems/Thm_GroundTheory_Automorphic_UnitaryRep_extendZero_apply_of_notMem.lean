-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_extendZero_apply_of_notMem
-- name    : GroundTheory.Automorphic.UnitaryRep.extendZero_apply_of_notMem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:42.897135+00:00
-- url     : https://prove2.me/theorems/43038750-0756-40dd-a1e1-2ff18f4e4859
-- title:
--   Unitary Rep: extend Zero apply of not Mem
-- statement:
--   The Unitary Rep construction uses the extend Zero apply of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L63-L66

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

theorem GroundTheory.Automorphic.UnitaryRep.extendZero_apply_of_notMem {L : Subgroup G} (hL : IsOpen (L : Set G))
    (f : CompactlySupportedContinuousMap L ℂ) {g : G} (hg : g ∉ L) : extendZero hL f g = 0 := by sorry
