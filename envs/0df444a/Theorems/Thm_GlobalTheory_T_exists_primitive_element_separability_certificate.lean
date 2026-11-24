-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_primitive_element_separability_certificate
-- name    : GlobalTheory.T.exists_primitive_element_separability_certificate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:38:26.086123+00:00
-- url     : https://prove2.me/theorems/7c6c12c5-288f-4374-8f43-c21a0e3060ee
-- title:
--   T: exists primitive element separability certificate
-- statement:
--   The T construction uses the exists primitive element separability certificate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificateStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificateStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificateStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_primitive_element_separability_certificate : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F), IsTranscendenceBasis k ((↑) : s → F) → Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F → ∀ T : Finset F, ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧ ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧ ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)), U * minpoly (Algebra.adjoin k (s : Set F)) θ + V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) = Polynomial.C H ∧ ∀ x ∈ T, (H : F) * x ∈ Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by sorry
