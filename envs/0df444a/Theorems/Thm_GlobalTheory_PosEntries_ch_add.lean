-- Prove2me | Theorems.Thm_GlobalTheory_PosEntries_ch_add
-- name    : GlobalTheory.PosEntries.ch_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:11:26.884959+00:00
-- url     : https://prove2.me/theorems/61ff4188-7a87-46de-a6e0-848865d2799d
-- title:
--   Pos Entries: ch add
-- statement:
--   The Pos Entries construction uses the ch add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeBlockDiagonalTargetEntryConditions.lean#L42-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions
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
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.PosEntries.ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by sorry
