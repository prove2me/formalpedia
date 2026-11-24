-- Prove2me | Theorems.Thm_GlobalTheory_T_linearIndependent_and_finrank_add_two_mul_of_hyperbolic
-- name    : GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:52:37.304513+00:00
-- url     : https://prove2.me/theorems/97f11275-05b5-460e-9396-839cb1b41a8c
-- title:
--   T: linear Independent and finrank add two mul of hyperbolic
-- statement:
--   The T construction uses the linear Independent and finrank add two mul of hyperbolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FinrankAddTwoMulOfHyperbolicPairsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FinrankAddTwoMulOfHyperbolicPairsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FinrankAddTwoMulOfHyperbolicPairs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FinrankAddTwoMulOfHyperbolicPairsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic : ∀ (E V : Type) [Field E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → ∀ (W : Submodule E V) (i : ℕ) (e f : Fin i → V), (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (f a) (f b) = 0) → (∀ a b, h (f a) (e b) = if a = b then 1 else 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0 ∧ h x (f a) = 0) → W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ → LinearIndependent E e ∧ Module.finrank E W + 2 * i = Module.finrank E V := by sorry
