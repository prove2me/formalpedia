-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_graded_of_mul_degree
-- name    : GlobalTheory.hasSum_graded_of_mul_degree
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:13.911289+00:00
-- url     : https://prove2.me/theorems/61bc759f-a8eb-4aeb-b54a-6a665ce7fa2e
-- title:
--   Global Theory: has Sum graded of mul degree
-- statement:
--   The Global Theory construction uses the has Sum graded of mul degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumGradedOfMulDegree.lean#L21-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumGradedOfMulDegree.lean#L21-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumGradedOfMulDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.hasSum_graded_of_mul_degree :
    ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) [AddCommGroup X] (Rel : ℕ → (X → C) → C → Prop) (n k : ℕ), 1 ≤ n → 1 ≤ k → (∀ (l l' : ℕ) (a a' : X → C) (c c' : C), 1 ≤ l → 1 ≤ l' → Rel l a c → Rel l' a' c' → ∃ a'', Rel (l + l') a'' (c * c') ∧ ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) → (∃ κ : C, κ ≠ 0 ∧ ∀ a c, Rel (n * k) a c → HasSum a (κ * c)) → ∃ u : C, u ≠ 0 ∧ ∀ a c, Rel k a c → Summable a → HasSum a (u * c) := by sorry
