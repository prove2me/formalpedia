-- Prove2me | Theorems.Thm_GlobalTheory_SymPattern_exists_of_pat
-- name    : GlobalTheory.SymPattern.exists_of_pat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:09.237667+00:00
-- url     : https://prove2.me/theorems/946ebecc-658c-4720-8974-038b16162f91
-- title:
--   Sym Pattern: exists of pat
-- statement:
--   The Sym Pattern construction uses the exists of pat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPattern.lean#L45-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPattern.lean#L45-L81

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

theorem GlobalTheory.SymPattern.exists_of_pat (ρ : ℕ) (gb : GL (Fin κ ⊕ Fin l) F)
    (h : ∀ a b, ¬ FreeTop ρ a b → gb.val a b = (1 : Matrix _ _ F) a b) :
    ∃ u : GL (Fin κ ⊕ Fin l) F, InN (ρ + 1) u ∧ ∃ γ : GL (Fin κ) F,
      IsUpperUnip Fin.val γ.val ∧ gb = u * embX l γ := by sorry
