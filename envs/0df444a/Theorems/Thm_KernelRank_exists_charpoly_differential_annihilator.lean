-- Prove2me | Theorems.Thm_KernelRank_exists_charpoly_differential_annihilator
-- name    : KernelRank.exists_charpoly_differential_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:07:22.014879+00:00
-- url     : https://prove2.me/theorems/380bc234-7dda-4e74-864b-55825a05fce9
-- title:
--   Kernel Rank: exists charpoly differential annihilator
-- statement:
--   The Kernel Rank construction uses the exists charpoly differential annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L71-L88
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L71-L88

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential
set_option autoImplicit true
open Polynomial NNReal
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace

theorem KernelRank.exists_charpoly_differential_annihilator (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = Module.finrank ℂ (translateSpan ψ) ∧
      ∀ t, 0 ≤ t → differentialOperator q ψ t = 0 := by sorry
