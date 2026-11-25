-- Prove2me | Theorems.Thm_GlobalTheory_InertField_isField_tensor_of_no_root
-- name    : GlobalTheory.InertField.isField_tensor_of_no_root
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:20.969795+00:00
-- url     : https://prove2.me/theorems/adf69fbc-fa49-46e5-a498-c1ef94e9c488
-- title:
--   Inert Field: is Field tensor of no root
-- statement:
--   The Inert Field construction uses the is Field tensor of no root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInert.lean#L9-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInert.lean#L9-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open GlobalTheory GlobalTheory.InertField

theorem GlobalTheory.InertField.isField_tensor_of_no_root {F K E : Type} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    (h2 : Module.finrank F E = 2) (a : E) (ha : ∀ x : F, algebraMap F E x ≠ a) (b c : F)
    (hq : a ^ 2 + algebraMap F E b * a + algebraMap F E c = 0)
    (hK : ∀ x : K, x ^ 2 + algebraMap F K b * x + algebraMap F K c ≠ 0) : IsField (K ⊗[F] E) := by sorry
