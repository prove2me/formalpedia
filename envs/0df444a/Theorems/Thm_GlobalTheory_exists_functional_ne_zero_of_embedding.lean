-- Prove2me | Theorems.Thm_GlobalTheory_exists_functional_ne_zero_of_embedding
-- name    : GlobalTheory.exists_functional_ne_zero_of_embedding
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:20.005272+00:00
-- url     : https://prove2.me/theorems/b8facd01-7987-4955-8a40-332e1f696d76
-- title:
--   Global Theory: exists functional ne zero of embedding
-- statement:
--   The Global Theory construction uses the exists functional ne zero of embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalMultiplierOfComplexMultiplier.lean#L48-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalMultiplierOfComplexMultiplier.lean#L48-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalMultiplierOfComplexMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module

theorem GlobalTheory.exists_functional_ne_zero_of_embedding (K : Type) [Field K] (σ : K →+* ℂ) (m : ℂ)
    (hm : m ≠ 0) : ∃ φ : ℂ →+ K, (∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c) ∧ φ m ≠ 0 := by sorry
