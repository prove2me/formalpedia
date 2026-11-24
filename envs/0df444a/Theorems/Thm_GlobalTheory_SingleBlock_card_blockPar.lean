-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_card_blockPar
-- name    : GlobalTheory.SingleBlock.card_blockPar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:22.335805+00:00
-- url     : https://prove2.me/theorems/1a7c61f9-e156-4651-9d90-4795fc989ba0
-- title:
--   Single Block: card block Par
-- statement:
--   The Single Block construction uses the card block Par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L69-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L69-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}

theorem GlobalTheory.SingleBlock.card_blockPar (Q : Subgroup (GL (Fin r) k)) :
    Nat.card (blockPar t Q) =
      Nat.card Q * (Nat.card k ^ (r * t) * Nat.card (GL (Fin t) k)) := by sorry
