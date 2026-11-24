-- Prove2me | Theorems.Thm_GlobalTheory_IsotropicVectorExistence_key
-- name    : GlobalTheory.IsotropicVectorExistence.key
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:21:52.9158+00:00
-- url     : https://prove2.me/theorems/91f79db3-cc01-4c16-947a-37b71b746932
-- title:
--   Isotropic Vector Existence: key
-- statement:
--   The Isotropic Vector Existence construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsBisLast.lean#L5-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsBisLast.lean#L5-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IsotropicVectorExistence

theorem GlobalTheory.IsotropicVectorExistence.key {z : ℂ} (k : ℕ) (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by sorry
