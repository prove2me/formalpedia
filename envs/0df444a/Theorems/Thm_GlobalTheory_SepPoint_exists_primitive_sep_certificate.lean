-- Prove2me | Theorems.Thm_GlobalTheory_SepPoint_exists_primitive_sep_certificate
-- name    : GlobalTheory.SepPoint.exists_primitive_sep_certificate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:32.42267+00:00
-- url     : https://prove2.me/theorems/280d1ea6-e075-47a3-af69-a39bd1434d17
-- title:
--   Sep Point: exists primitive sep certificate
-- statement:
--   The Sep Point construction uses the exists primitive sep certificate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L50-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L50-L140

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

theorem GlobalTheory.SepPoint.exists_primitive_sep_certificate (k F : Type) [Field k] [Field F] [Algebra k F]
    (s : Finset F) (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F) (T : Finset F) :
    ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧
      ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧
        ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)),
          U * minpoly (Algebra.adjoin k (s : Set F)) θ +
              V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) =
            Polynomial.C H ∧
          ∀ x ∈ T, (H : F) * x ∈
            Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by sorry
