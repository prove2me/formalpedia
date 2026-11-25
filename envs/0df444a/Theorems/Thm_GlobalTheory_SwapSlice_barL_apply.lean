-- Prove2me | Theorems.Thm_GlobalTheory_SwapSlice_barL_apply
-- name    : GlobalTheory.SwapSlice.barL_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:27.336012+00:00
-- url     : https://prove2.me/theorems/a0b8f283-50ea-4935-904c-13ac1d7ba138
-- title:
--   Swap Slice: bar L apply
-- statement:
--   The Swap Slice construction uses the bar L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SwapNegApply.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SwapNegApply.lean#L29-L30

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

theorem GlobalTheory.SwapSlice.barL_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ → k) → ℂ) (y : Y) :
    barL ι Φ y = starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y) := by sorry
