-- Prove2me | Theorems.Thm_GlobalTheory_FourTermSumReorder_sum_four_reorder
-- name    : GlobalTheory.FourTermSumReorder.sum_four_reorder
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:22.620162+00:00
-- url     : https://prove2.me/theorems/a1a92df1-fc9f-5e78-a18b-0b8a9f067345
-- title:
--   Four Term Sum Reorder: sum four reorder
-- statement:
--   The Four Term Sum Reorder construction uses the sum four reorder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumFourReorder.lean#L5-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumFourReorder.lean#L5-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumFourReorder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FourTermSumReorder

theorem GlobalTheory.FourTermSumReorder.sum_four_reorder {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by sorry
