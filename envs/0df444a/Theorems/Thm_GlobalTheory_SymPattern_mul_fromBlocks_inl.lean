-- Prove2me | Theorems.Thm_GlobalTheory_SymPattern_mul_fromBlocks_inl
-- name    : GlobalTheory.SymPattern.mul_fromBlocks_inl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:15.213637+00:00
-- url     : https://prove2.me/theorems/1bb8468f-b82c-4fb4-a52f-7dec2f42a0c5
-- title:
--   Sym Pattern: mul from Blocks inl
-- statement:
--   The Sym Pattern construction uses the mul from Blocks inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPattern.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPattern.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {F : Type} [Field F] {κ l : ℕ}

theorem GlobalTheory.SymPattern.mul_fromBlocks_inl (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin κ) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inl j) = ∑ t, M a (Sum.inl t) * C t j := by sorry
