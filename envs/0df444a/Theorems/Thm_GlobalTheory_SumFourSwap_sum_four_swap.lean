-- Prove2me | Theorems.Thm_GlobalTheory_SumFourSwap_sum_four_swap
-- name    : GlobalTheory.SumFourSwap.sum_four_swap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:31.409273+00:00
-- url     : https://prove2.me/theorems/6f12c9c9-cb79-58f7-a41f-10d8878651b0
-- title:
--   Sum Four Swap: sum four swap
-- statement:
--   The Sum Four Swap construction uses the sum four swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SumFourSwap.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SumFourSwap.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SumFourSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SumFourSwap

theorem GlobalTheory.SumFourSwap.sum_four_swap {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by sorry
