-- Prove2me | Theorems.Thm_KernelRank_finrank_translateSpan_ofReal
-- name    : KernelRank.finrank_translateSpan_ofReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:06:27.701796+00:00
-- url     : https://prove2.me/theorems/ae34b236-64d9-4474-a370-b2a63b9abbc5
-- title:
--   Kernel Rank: finrank translate Span of Real
-- statement:
--   The Kernel Rank construction uses the finrank translate Span of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L63-L74
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L63-L74

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

theorem KernelRank.finrank_translateSpan_ofReal (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] :
    Module.finrank ℂ (translateSpan (fun t => (φ t : ℂ))) =
      Module.finrank ℝ (translateSpan φ) := by sorry
