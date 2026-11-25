-- Prove2me | Theorems.Thm_GlobalTheory_FiniteExtensionEmbedding_exists_finite_extension_embedding
-- name    : GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:11.624689+00:00
-- url     : https://prove2.me/theorems/3e6d4cc6-1eb6-4876-b3ea-f2a8a61f6dfd
-- title:
--   Finite Extension Embedding: exists finite extension embedding
-- statement:
--   The Finite Extension Embedding construction uses the exists finite extension embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionEmbedding.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionEmbedding.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtensionEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.FiniteExtensionEmbedding

theorem GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding (F K : Type) [Field F] [CharZero F]
    [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by sorry
