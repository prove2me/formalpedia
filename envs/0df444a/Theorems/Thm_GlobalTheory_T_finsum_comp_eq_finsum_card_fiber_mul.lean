-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_comp_eq_finsum_card_fiber_mul
-- name    : GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:44.200801+00:00
-- url     : https://prove2.me/theorems/dadc690a-baf1-4957-8541-1d983c2f63f4
-- title:
--   T: finsum comp eq finsum card fiber mul
-- statement:
--   The T construction uses the finsum comp eq finsum card fiber mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumCompEqFinsumCardFiberMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumCompEqFinsumCardFiberMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul : ∀ {X Y : Type} (π : X → Y) (h : Y → ℂ), ((∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) → ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by sorry
