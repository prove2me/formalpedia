-- Prove2me | Theorems.Thm_GlobalTheory_exists_rep_mod_shifted_form_small
-- name    : GlobalTheory.exists_rep_mod_shifted_form_small
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:10.362272+00:00
-- url     : https://prove2.me/theorems/9d61e3a8-e411-50a7-b6c0-d98ed904f65a
-- title:
--   Global Theory: exists rep mod shifted form small
-- statement:
--   The Global Theory construction uses the exists rep mod shifted form small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSmulEqBilinOfAnisotropic.lean#L51-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSmulEqBilinOfAnisotropic.lean#L51-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqBilinOfAnisotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_rep_mod_shifted_form_small :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (l : X →+ ℚ) (k : ℕ), 1 ≤ k → ∀ y : X, ∃ z : X, ∀ m : X, |(B (y + k • z) m : ℚ) - l m| ≤ k * Q m := by sorry
