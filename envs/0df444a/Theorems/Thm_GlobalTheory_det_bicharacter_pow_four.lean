-- Prove2me | Theorems.Thm_GlobalTheory_det_bicharacter_pow_four
-- name    : GlobalTheory.det_bicharacter_pow_four
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:53.462421+00:00
-- url     : https://prove2.me/theorems/b3934105-08da-442c-9f60-3449dd94ff38
-- title:
--   Global Theory: det bicharacter pow four
-- statement:
--   The Global Theory construction uses the det bicharacter pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetBicharacterPowFour.lean#L38-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetBicharacterPowFour.lean#L38-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetBicharacterPowFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.det_bicharacter_pow_four :
    ∀ (Γ K : Type) [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K] (X : Γ → Γ → K), (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → (Matrix.of X).det ^ 4 = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by sorry
