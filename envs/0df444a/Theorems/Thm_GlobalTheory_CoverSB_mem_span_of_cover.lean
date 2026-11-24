-- Prove2me | Theorems.Thm_GlobalTheory_CoverSB_mem_span_of_cover
-- name    : GlobalTheory.CoverSB.mem_span_of_cover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:44.455953+00:00
-- url     : https://prove2.me/theorems/7485185f-7e03-49b7-8836-a6302cdeb999
-- title:
--   Cover SB: mem span of cover
-- statement:
--   The Cover SB construction uses the mem span of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatPartitionOfUnity.lean#L58-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatPartitionOfUnity.lean#L58-L96

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

theorem GlobalTheory.CoverSB.mem_span_of_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by sorry
