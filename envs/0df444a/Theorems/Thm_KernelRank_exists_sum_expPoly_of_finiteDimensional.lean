-- Prove2me | Theorems.Thm_KernelRank_exists_sum_expPoly_of_finiteDimensional
-- name    : KernelRank.exists_sum_expPoly_of_finiteDimensional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:06:19.872329+00:00
-- url     : https://prove2.me/theorems/8f12f26b-39b7-42ea-8265-4efe89b1b49b
-- title:
--   Kernel Rank: exists sum exp Poly of finite Dimensional
-- statement:
--   A continuous complex profile with finite-dimensional translate span is an exponential sum.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Necessity.lean#L75-L97
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Necessity.lean#L75-L97

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Representation
import Definitions.Def_KernelRankLean_Necessity
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem KernelRank.exists_sum_expPoly_of_finiteDimensional (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ S : Finset ℂ, ∃ Q : ℂ → ℂ[X], ∀ t, 0 ≤ t → ψ t = ∑ μ ∈ S, expPoly (Q μ) μ t := by sorry
