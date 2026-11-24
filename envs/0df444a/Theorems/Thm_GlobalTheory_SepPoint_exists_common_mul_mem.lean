-- Prove2me | Theorems.Thm_GlobalTheory_SepPoint_exists_common_mul_mem
-- name    : GlobalTheory.SepPoint.exists_common_mul_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:26.496184+00:00
-- url     : https://prove2.me/theorems/c9b260fc-e48e-4355-a36c-7b8f59c0992d
-- title:
--   Sep Point: exists common mul mem
-- statement:
--   The Sep Point construction uses the exists common mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L29-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
open GlobalTheory GlobalTheory.SepPoint

theorem GlobalTheory.SepPoint.exists_common_mul_mem {k F : Type} [Field k] [Field F] [Algebra k F]
    (R S : Subalgebra k F) (hRS : R ≤ S) (T : Finset F)
    (h : ∀ x ∈ T, ∃ b : R, b ≠ 0 ∧ (b : F) * x ∈ S) :
    ∃ B : R, B ≠ 0 ∧ ∀ x ∈ T, (B : F) * x ∈ S := by sorry
