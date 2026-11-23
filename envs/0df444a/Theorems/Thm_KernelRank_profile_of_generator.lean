-- Prove2me | Theorems.Thm_KernelRank_profile_of_generator
-- name    : KernelRank.profile_of_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:06:39.717816+00:00
-- url     : https://prove2.me/theorems/bb6e8f0f-148f-4e9c-aa37-d2fd2a288024
-- title:
--   Kernel Rank: profile of generator
-- statement:
--   The Kernel Rank construction uses the profile of generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L157-L163
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L157-L163

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

theorem KernelRank.profile_of_generator (A : translateSpan ψ →L[ℂ] translateSpan ψ)
    (hA : ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • A))
    {t : ℝ} (ht : 0 ≤ t) :
    ψ t = evalW ψ 0 (NormedSpace.exp ((t : ℂ) • A) (initialProfile ψ)) := by sorry
