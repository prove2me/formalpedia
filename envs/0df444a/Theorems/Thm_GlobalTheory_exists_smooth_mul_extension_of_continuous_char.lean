-- Prove2me | Theorems.Thm_GlobalTheory_exists_smooth_mul_extension_of_continuous_char
-- name    : GlobalTheory.exists_smooth_mul_extension_of_continuous_char
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:19.352394+00:00
-- url     : https://prove2.me/theorems/660930ee-5c36-4051-9a52-c9a692de2409
-- title:
--   Global Theory: exists smooth mul extension of continuous char
-- statement:
--   The Global Theory construction uses the exists smooth mul extension of continuous char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSmoothMulExtensionOfContinuousChar.lean#L110-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSmoothMulExtensionOfContinuousChar.lean#L110-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.exists_smooth_mul_extension_of_continuous_char :
    ∀ (K : Type) [Field K] [NumberField K] (ψ : (mixedSpace K)ˣ →* ℂˣ), Continuous ψ → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ u : (mixedSpace K)ˣ, φ u = (ψ u : ℂ)) ∧ ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by sorry
