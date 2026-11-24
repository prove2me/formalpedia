-- Prove2me | Theorems.Thm_GlobalTheory_exists_span_singleton_eq_map_of_integral
-- name    : GlobalTheory.exists_span_singleton_eq_map_of_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:16.6712+00:00
-- url     : https://prove2.me/theorems/2bddab31-4e67-487d-bc60-4106d8f18343
-- title:
--   Global Theory: exists span singleton eq map of integral
-- statement:
--   The Global Theory construction uses the exists span singleton eq map of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SumLogNormEmbeddingEqFinrankMulLogAbsNorm.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SumLogNormEmbeddingEqFinrankMulLogAbsNorm.lean#L7-L62

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

theorem GlobalTheory.exists_span_singleton_eq_map_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∃ β₀ : 𝓞 M, (β₀ : M) = β ∧ Ideal.span {β₀} = 𝔟.map (algebraMap (𝓞 K) (𝓞 M)) := by sorry
