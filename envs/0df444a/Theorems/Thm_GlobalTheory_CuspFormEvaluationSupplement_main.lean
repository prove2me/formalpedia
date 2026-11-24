-- Prove2me | Theorems.Thm_GlobalTheory_CuspFormEvaluationSupplement_main
-- name    : GlobalTheory.CuspFormEvaluationSupplement.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:28.062924+00:00
-- url     : https://prove2.me/theorems/42062e96-58d7-4da4-afdf-fa0b9a2b275d
-- title:
--   Cusp Form Evaluation Supplement: main
-- statement:
--   The Cusp Form Evaluation Supplement construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/Imports.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/Imports.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspFormEvaluationSupplement
universe u_1

theorem GlobalTheory.CuspFormEvaluationSupplement.main : ∀ {R : Type u_1} [inst : CommRing R] {P : Ideal R}, Ideal.IsPrime P → ∀ (N : ℕ), N ≠ (0 : ℕ) → (↑N : R) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ N ∧ (↑p : R) ∈ P := by sorry
