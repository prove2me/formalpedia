-- Prove2me | Theorems.Thm_GlobalTheory_T_not_isField_adicCompletion_tensor_of_split
-- name    : GlobalTheory.T.not_isField_adicCompletion_tensor_of_split
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:54:39.183635+00:00
-- url     : https://prove2.me/theorems/1fe3c568-047b-4aff-a159-4b4a686c0265
-- title:
--   T: not is Field adic Completion tensor of split
-- statement:
--   The T construction uses the not is Field adic Completion tensor of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NotIsFieldAdicCompletionTensorOfSplitStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NotIsFieldAdicCompletionTensorOfSplitStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplitStatement
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

theorem GlobalTheory.T.not_isField_adicCompletion_tensor_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.primesOver (𝓞 E)).ncard = 2 → ¬ IsField (v.adicCompletion F ⊗[F] E) := by sorry
