-- Prove2me | Theorems.Thm_GlobalTheory_T_cartierPropertyAt_sign_mul_factorial_scaling
-- name    : GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:39.436463+00:00
-- url     : https://prove2.me/theorems/82c7c6e0-135e-4e70-b36b-25731b9f56d3
-- title:
--   T: cartier Property At sign mul factorial scaling
-- statement:
--   The T construction uses the cartier Property At sign mul factorial scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CartierPropertyAtSignMulFactorialScalingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CartierPropertyAtSignMulFactorialScalingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartierPropertyAtSignMulFactorialScaling
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartierPropertyAtSignMulFactorialScalingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E) (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) → (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by sorry
