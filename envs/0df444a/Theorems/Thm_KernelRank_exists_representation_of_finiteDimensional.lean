-- Prove2me | Theorems.Thm_KernelRank_exists_representation_of_finiteDimensional
-- name    : KernelRank.exists_representation_of_finiteDimensional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:12:22.054497+00:00
-- url     : https://prove2.me/theorems/5fff1269-d9c1-4395-a683-a918cb3e945d
-- title:
--   Kernel Rank: exists representation of finite Dimensional
-- statement:
--   **Necessity.** A profile, continuous on `[0, ∞)`, whose translates span a finite-dimensional
--   space is, on `[0, ∞)`, the profile of a representation.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Necessity.lean#L101-L108
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Necessity.lean#L101-L108

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Representation
import Definitions.Def_KernelRankLean_Necessity
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem KernelRank.exists_representation_of_finiteDimensional (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0))
    [FiniteDimensional ℝ (translateSpan φ)] :
    ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s := by sorry
