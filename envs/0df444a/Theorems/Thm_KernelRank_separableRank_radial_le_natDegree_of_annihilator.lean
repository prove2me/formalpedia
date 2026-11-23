-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_le_natDegree_of_annihilator
-- name    : KernelRank.separableRank_radial_le_natDegree_of_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:35:18.399263+00:00
-- url     : https://prove2.me/theorems/cf484910-f03a-4bea-8a80-22e64f90cc02
-- title:
--   Kernel Rank: separable Rank radial le nat Degree of annihilator
-- statement:
--   No nonzero constant-coefficient annihilator has order below the 2-D radial kernel's rank.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Annihilator.lean#L60-L67
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Annihilator.lean#L60-L67

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_Annihilator
set_option autoImplicit true
open Polynomial NNReal
open KernelRank

theorem KernelRank.separableRank_radial_le_natDegree_of_annihilator (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)]
    (hφ : ContinuousOn φ (Set.Ici 0)) {q : ℂ[X]} (hq : q ≠ 0)
    (hann : ∀ t, 0 ≤ t → differentialOperator q (fun s => (φ s : ℂ)) t = 0) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) ≤ q.natDegree := by sorry
