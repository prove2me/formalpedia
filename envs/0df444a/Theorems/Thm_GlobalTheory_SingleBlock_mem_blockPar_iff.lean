-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_mem_blockPar_iff
-- name    : GlobalTheory.SingleBlock.mem_blockPar_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:03.842956+00:00
-- url     : https://prove2.me/theorems/0356e3fd-046a-4d17-a9a8-eaaab449d0e5
-- title:
--   Single Block: mem block Par iff
-- statement:
--   The Single Block construction uses the mem block Par iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FromBlocksMulInv.lean#L47-L67

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

theorem GlobalTheory.SingleBlock.mem_blockPar_iff (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔
      (∃ p ∈ Q, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₁ =
        (p : Matrix (Fin r) (Fin r) k)) ∧
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₁ = 0 := by sorry
