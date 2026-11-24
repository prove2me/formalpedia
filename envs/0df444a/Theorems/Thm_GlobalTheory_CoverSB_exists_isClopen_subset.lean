-- Prove2me | Theorems.Thm_GlobalTheory_CoverSB_exists_isClopen_subset
-- name    : GlobalTheory.CoverSB.exists_isClopen_subset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:02.403253+00:00
-- url     : https://prove2.me/theorems/b3ddc6e9-c7e6-45c9-a334-c969b32ccc78
-- title:
--   Cover SB: exists is Clopen subset
-- statement:
--   The Cover SB construction uses the exists is Clopen subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatPartitionOfUnity.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatPartitionOfUnity.lean#L38-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CoverSB.exists_isClopen_subset {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    {U : Set (Matrix A D k)} (hU : IsOpen U) {x : Matrix A D k} (hx : x ∈ U) :
    ∃ V : Set (Matrix A D k), IsClopen V ∧ x ∈ V ∧ V ⊆ U := by sorry
