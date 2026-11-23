-- Prove2me | Theorems.Thm_KernelRank_generator_apply
-- name    : KernelRank.generator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:07:15.446303+00:00
-- url     : https://prove2.me/theorems/6f2b9078-2a72-45fb-b32f-13d7edc17cb6
-- title:
--   Kernel Rank: generator apply
-- statement:
--   The Kernel Rank construction uses the generator apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L150-L155
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L150-L155

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup
set_option autoImplicit true
open NNReal
open KernelRank
variable {𝕜 : Type*} [Field 𝕜]
variable (φ : ℝ → 𝕜)
variable (ψ : ℝ → ℂ) [FiniteDimensional ℂ (translateSpan ψ)]
attribute [local instance] translateNormedAddCommGroup translateNormedSpace translateUniformSpace
attribute [local instance] translateCompleteSpace

theorem KernelRank.generator_apply (A : translateSpan ψ →L[ℂ] translateSpan ψ)
    (hA : ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • A))
    (g : translateSpan ψ) {t : ℝ} (ht : 0 ≤ t) (u : ℝ≥0) :
    (NormedSpace.exp ((t : ℂ) • A) g).1 u = g.1 (u + t.toNNReal) := by sorry
