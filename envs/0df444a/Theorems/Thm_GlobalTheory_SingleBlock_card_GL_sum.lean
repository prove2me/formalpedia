-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_card_GL_sum
-- name    : GlobalTheory.SingleBlock.card_GL_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:19.486182+00:00
-- url     : https://prove2.me/theorems/c19e4cad-1de2-4467-80cc-db2dd72a3128
-- title:
--   Single Block: card GL sum
-- statement:
--   The Single Block construction uses the card GL sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L138-L140

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

theorem GlobalTheory.SingleBlock.card_GL_sum : Nat.card (GL (Fin r ⊕ Fin t) k) = Nat.card (GL (Fin (r + t)) k) := by sorry
