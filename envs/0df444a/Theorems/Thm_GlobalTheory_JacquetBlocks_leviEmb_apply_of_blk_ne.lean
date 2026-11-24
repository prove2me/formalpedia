-- Prove2me | Theorems.Thm_GlobalTheory_JacquetBlocks_leviEmb_apply_of_blk_ne
-- name    : GlobalTheory.JacquetBlocks.leviEmb_apply_of_blk_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:52:56.747273+00:00
-- url     : https://prove2.me/theorems/ed3e0894-e847-4d91-ace0-0b58e210b3c7
-- title:
--   Jacquet Blocks: levi Emb apply of blk ne
-- statement:
--   The Jacquet Blocks construction uses the levi Emb apply of blk ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L64-L68

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
omit [LinearOrder α]

theorem GlobalTheory.JacquetBlocks.leviEmb_apply_of_blk_ne (e : (Σ a, m a) ≃ n) (g : Levi R m) {i j : n}
    (h : blk e i ≠ blk e j) : (leviEmb R e g : Matrix n n R) i j = 0 := by sorry
