-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_card_GL_real
-- name    : GlobalTheory.SingleBlock.card_GL_real
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:19.178581+00:00
-- url     : https://prove2.me/theorems/1d4f9c2f-5f8e-42dd-97a6-48926463055f
-- title:
--   Single Block: card GL real
-- statement:
--   The Single Block construction uses the card GL real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L97-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L97-L136

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

theorem GlobalTheory.SingleBlock.card_GL_real [Finite k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Nat.card k : ℝ) ^ (n * n) *
      ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by sorry
