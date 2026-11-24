-- Prove2me | Theorems.Thm_GlobalTheory_T_isRegularLocalRing_localization_atPrime_tensor_field
-- name    : GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:11.70492+00:00
-- url     : https://prove2.me/theorems/e46a8d98-0a98-4e62-b335-e9df8e3c0b0b
-- title:
--   T: is Regular Local Ring localization at Prime tensor field
-- statement:
--   The T construction uses the is Regular Local Ring localization at Prime tensor field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingAtPrimeLocalizationTensorStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingAtPrimeLocalizationTensorStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by sorry
