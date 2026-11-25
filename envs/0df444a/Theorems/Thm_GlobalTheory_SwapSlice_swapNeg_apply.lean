-- Prove2me | Theorems.Thm_GlobalTheory_SwapSlice_swapNeg_apply
-- name    : GlobalTheory.SwapSlice.swapNeg_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:05.920813+00:00
-- url     : https://prove2.me/theorems/f37a1b99-d58f-4200-8c81-66aa7327cad1
-- title:
--   Swap Slice: swap Neg apply
-- statement:
--   The Swap Slice construction uses the swap Neg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SwapNegApply.lean#L62-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SwapNegApply.lean#L62-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SwapNegApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SwapSlice
open GlobalTheory.WeilM
variable {k κ Y : Type}

theorem GlobalTheory.SwapSlice.swapNeg_apply [Neg Y] (Z : Y × Y) : swapNeg Z = (-Z.2, -Z.1) := by sorry
