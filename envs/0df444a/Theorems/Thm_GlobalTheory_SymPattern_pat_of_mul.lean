-- Prove2me | Theorems.Thm_GlobalTheory_SymPattern_pat_of_mul
-- name    : GlobalTheory.SymPattern.pat_of_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:31.050893+00:00
-- url     : https://prove2.me/theorems/2d38d5c6-cfcf-4f00-88d1-c2f31b7e2aed
-- title:
--   Sym Pattern: pat of mul
-- statement:
--   The Sym Pattern construction uses the pat of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPattern.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemLevelIffSymmetricPositionEntryPattern.lean#L24-L43

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

theorem GlobalTheory.SymPattern.pat_of_mul (ρ : ℕ) (u : GL (Fin κ ⊕ Fin l) F) (hu : InN (ρ + 1) u) (γ : GL (Fin κ) F)
    (hγ : IsUpperUnip Fin.val γ.val) :
    ∀ a b, ¬ FreeTop ρ a b → (u * embX l γ).val a b = (1 : Matrix _ _ F) a b := by sorry
