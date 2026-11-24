-- Prove2me | Theorems.Thm_GlobalTheory_isRegularLocalRing_atPrime_localization_tensor
-- name    : GlobalTheory.isRegularLocalRing_atPrime_localization_tensor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:26.626419+00:00
-- url     : https://prove2.me/theorems/7252513f-766b-4c29-8dbb-3f81e502cd04
-- title:
--   Global Theory: is Regular Local Ring at Prime localization tensor
-- statement:
--   The Global Theory construction uses the is Regular Local Ring at Prime localization tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingAtPrimeLocalizationTensor.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingAtPrimeLocalizationTensor.lean#L22-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensor
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
open GlobalTheory

theorem GlobalTheory.isRegularLocalRing_atPrime_localization_tensor : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by sorry
