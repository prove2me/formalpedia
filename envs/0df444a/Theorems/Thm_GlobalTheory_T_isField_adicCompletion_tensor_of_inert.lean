-- Prove2me | Theorems.Thm_GlobalTheory_T_isField_adicCompletion_tensor_of_inert
-- name    : GlobalTheory.T.isField_adicCompletion_tensor_of_inert
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:57.94497+00:00
-- url     : https://prove2.me/theorems/71cb633c-a8f6-4eed-8c4b-293d1e9a0bd7
-- title:
--   T: is Field adic Completion tensor of inert
-- statement:
--   The T construction uses the is Field adic Completion tensor of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInertStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldAdicCompletionTensorOfInertStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInertStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isField_adicCompletion_tensor_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime → IsField (v.adicCompletion F ⊗[F] E) := by sorry
