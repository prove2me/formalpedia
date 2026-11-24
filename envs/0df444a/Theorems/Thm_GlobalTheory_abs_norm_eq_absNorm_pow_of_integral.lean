-- Prove2me | Theorems.Thm_GlobalTheory_abs_norm_eq_absNorm_pow_of_integral
-- name    : GlobalTheory.abs_norm_eq_absNorm_pow_of_integral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:18.951179+00:00
-- url     : https://prove2.me/theorems/02b9dd15-1694-4755-8c34-28b7110ee519
-- title:
--   Global Theory: abs norm eq abs Norm pow of integral
-- statement:
--   The Global Theory construction uses the abs norm eq abs Norm pow of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SumLogNormEmbeddingEqFinrankMulLogAbsNorm.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SumLogNormEmbeddingEqFinrankMulLogAbsNorm.lean#L64-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.abs_norm_eq_absNorm_pow_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    |Algebra.norm ℚ β| = (Ideal.absNorm 𝔟 : ℚ) ^ Module.finrank K M := by sorry
