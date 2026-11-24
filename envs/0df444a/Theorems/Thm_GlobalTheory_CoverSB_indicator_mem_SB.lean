-- Prove2me | Theorems.Thm_GlobalTheory_CoverSB_indicator_mem_SB
-- name    : GlobalTheory.CoverSB.indicator_mem_SB
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:37.007685+00:00
-- url     : https://prove2.me/theorems/0aa27078-85ca-45af-bf53-4122b79e1257
-- title:
--   Cover SB: indicator mem SB
-- statement:
--   The Cover SB construction uses the indicator mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatPartitionOfUnity.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatPartitionOfUnity.lean#L14-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
import Theorems.Thm_GlobalTheory_SplitWeil_Model_indicator_mem_SB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CoverSB

theorem GlobalTheory.CoverSB.indicator_mem_SB {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) {g : X → ℂ}
    (hg : g ∈ SB X) : W.indicator g ∈ SB X := by sorry
