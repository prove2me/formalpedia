-- Prove2me | Theorems.Thm_KernelRank_continuous_shiftCLM
-- name    : KernelRank.continuous_shiftCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:06:11.371883+00:00
-- url     : https://prove2.me/theorems/b74a9f1e-aca7-4d4f-9994-426922ecc2be
-- title:
--   Kernel Rank: continuous shift CLM
-- statement:
--   The Kernel Rank construction uses the continuous shift CLM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L120-L126
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean#L120-L126

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

theorem KernelRank.continuous_shiftCLM (hψ : ContinuousOn ψ (Set.Ici 0)) : Continuous (shiftCLM ψ) := by sorry
