-- Prove2me | Theorems.Thm_GlobalTheory_exists_det_add_mul_ne_zero_of_ker_inf
-- name    : GlobalTheory.exists_det_add_mul_ne_zero_of_ker_inf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:53.930874+00:00
-- url     : https://prove2.me/theorems/e30742dd-7e3b-4bdd-92f5-1b81bf6d8527
-- title:
--   Global Theory: exists det add mul ne zero of ker inf
-- statement:
--   The Global Theory construction uses the exists det add mul ne zero of ker inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualPairIsUnitDetBlocks.lean#L6-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualPairIsUnitDetBlocks.lean#L6-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualPairIsUnitDetBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.exists_det_add_mul_ne_zero_of_ker_inf {k : Type} [Field k] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) k)
    (h : ∀ v : Fin n → k, A *ᵥ v = 0 → C *ᵥ v = 0 → v = 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, (A + X * C).det ≠ 0 := by sorry
