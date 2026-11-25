-- Prove2me | Theorems.Thm_GlobalTheory_FourTermSumSwap_sum_four_swap
-- name    : GlobalTheory.FourTermSumSwap.sum_four_swap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:27.354216+00:00
-- url     : https://prove2.me/theorems/3e890941-10a6-5e9e-a163-d40a703db7d0
-- title:
--   Four Term Sum Swap: sum four swap
-- statement:
--   The Four Term Sum Swap construction uses the sum four swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumFourSwap.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumFourSwap.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumFourSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FourTermSumSwap

theorem GlobalTheory.FourTermSumSwap.sum_four_swap : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β]
    (f : α → β → α → β → R),
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by sorry
