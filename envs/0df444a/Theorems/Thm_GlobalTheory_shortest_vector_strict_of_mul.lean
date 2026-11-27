-- Prove2me | Theorems.Thm_GlobalTheory_shortest_vector_strict_of_mul
-- name    : GlobalTheory.shortest_vector_strict_of_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:08.811506+00:00
-- url     : https://prove2.me/theorems/7d7552c9-2b34-4a3b-b7c2-b2943508f1eb
-- title:
--   Global Theory: shortest vector strict of mul
-- statement:
--   The Global Theory construction uses the shortest vector strict of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ShortestVectorStrictOfMul.lean#L5-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ShortestVectorStrictOfMul.lean#L5-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ShortestVectorStrictOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.shortest_vector_strict_of_mul :
    ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (n r : ℕ), 1 ≤ n → 2 ≤ r → ∀ z : X, (∀ m, Q z ≤ Q (z + n • m)) → ∀ m : X, (n * r) • m ≠ 0 → Q z < Q (z + (n * r) • m) := by sorry
