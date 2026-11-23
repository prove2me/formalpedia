-- Prove2me | Theorems.Thm_KernelRank_continuous_of_mem_translateSpan
-- name    : KernelRank.continuous_of_mem_translateSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:06:22.328902+00:00
-- url     : https://prove2.me/theorems/8581e127-9518-43d1-8e73-8485eb47896e
-- title:
--   Kernel Rank: continuous of mem translate Span
-- statement:
--   The Kernel Rank construction uses the continuous of mem translate Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L109-L118
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L109-L118

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
omit [FiniteDimensional ℂ (translateSpan ψ)]

theorem KernelRank.continuous_of_mem_translateSpan (hψ : ContinuousOn ψ (Set.Ici 0))
    {g : ℝ≥0 → ℂ} (hg : g ∈ translateSpan ψ) : Continuous g := by sorry
