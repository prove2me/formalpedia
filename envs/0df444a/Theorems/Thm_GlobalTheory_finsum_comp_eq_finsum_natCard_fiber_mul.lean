-- Prove2me | Theorems.Thm_GlobalTheory_finsum_comp_eq_finsum_natCard_fiber_mul
-- name    : GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:36:29.993014+00:00
-- url     : https://prove2.me/theorems/de00279e-99dd-4893-8a94-b7078a68da06
-- title:
--   Global Theory: finsum comp eq finsum nat Card fiber mul
-- statement:
--   The Global Theory construction uses the finsum comp eq finsum nat Card fiber mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumCompEqFinsumCardFiberMul.lean#L6-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumCompEqFinsumCardFiberMul.lean#L6-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul {X Y : Type} (π : X → Y) (h : Y → ℂ)
    (hf : (∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) :
    ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by sorry
