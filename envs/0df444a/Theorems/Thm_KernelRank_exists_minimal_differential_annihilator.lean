-- Prove2me | Theorems.Thm_KernelRank_exists_minimal_differential_annihilator
-- name    : KernelRank.exists_minimal_differential_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:12:27.89038+00:00
-- url     : https://prove2.me/theorems/e645b63c-d653-4b7e-99fa-8f8428862300
-- title:
--   Kernel Rank: exists minimal differential annihilator
-- statement:
--   The least differential-annihilator order is the 2-D radial kernel's separable rank.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Annihilator.lean#L17-L57
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Annihilator.lean#L17-L57

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_Annihilator
set_option autoImplicit true
open Polynomial NNReal
open KernelRank

theorem KernelRank.exists_minimal_differential_annihilator (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] (hφ : ContinuousOn φ (Set.Ici 0)) :
    ∃ p : ℂ[X], p.Monic ∧
      separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) = p.natDegree ∧
      ∀ q : ℂ[X],
        (∀ t, 0 ≤ t → differentialOperator q (fun s => (φ s : ℂ)) t = 0) ↔ p ∣ q := by sorry
