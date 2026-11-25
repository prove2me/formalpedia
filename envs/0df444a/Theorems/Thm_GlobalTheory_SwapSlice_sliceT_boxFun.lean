-- Prove2me | Theorems.Thm_GlobalTheory_SwapSlice_sliceT_boxFun
-- name    : GlobalTheory.SwapSlice.sliceT_boxFun
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:01.939696+00:00
-- url     : https://prove2.me/theorems/51d419c8-9454-40ba-9309-e026bb1e4a08
-- title:
--   Swap Slice: slice T box Fun
-- statement:
--   The Swap Slice construction uses the slice T box Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SwapNegApply.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SwapNegApply.lean#L64-L73

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

theorem GlobalTheory.SwapSlice.sliceT_boxFun [CommRing k] (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ₁ φ₂ : (κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι (boxFun φ₁ φ₂) Z = ι φ₁ Z.1 * barL ι φ₂ Z.2 := by sorry
