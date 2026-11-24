-- Prove2me | Theorems.Thm_GlobalTheory_finrank_add_two_mul_of_hyperbolic_pairs
-- name    : GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:20.496272+00:00
-- url     : https://prove2.me/theorems/74b6efb3-2168-465f-93ce-d9566dcc0cce
-- title:
--   Global Theory: finrank add two mul of hyperbolic pairs
-- statement:
--   The Global Theory construction uses the finrank add two mul of hyperbolic pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FinrankAddTwoMulOfHyperbolicPairs.lean#L5-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FinrankAddTwoMulOfHyperbolicPairs.lean#L5-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FinrankAddTwoMulOfHyperbolicPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs :
    ∀ (E V : Type) [Field E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → ∀ (W : Submodule E V) (i : ℕ) (e f : Fin i → V), (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (f a) (f b) = 0) → (∀ a b, h (f a) (e b) = if a = b then 1 else 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0 ∧ h x (f a) = 0) → W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ → LinearIndependent E e ∧ Module.finrank E W + 2 * i = Module.finrank E V := by sorry
