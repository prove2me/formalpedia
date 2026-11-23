-- Prove2me | Theorems.Thm_KernelRank_shiftW_apply
-- name    : KernelRank.shiftW_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:05:59.942365+00:00
-- url     : https://prove2.me/theorems/9df5888e-b9c9-4642-a85e-dcd98a4f6446
-- title:
--   Kernel Rank: shift W apply
-- statement:
--   The Kernel Rank construction uses the shift W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L46-L47
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L46-L47

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

theorem KernelRank.shiftW_apply (t : ℝ≥0) (g : translateSpan φ) (u : ℝ≥0) :
    (shiftW φ t g : ℝ≥0 → 𝕜) u = (g : ℝ≥0 → 𝕜) (u + t) := by sorry
