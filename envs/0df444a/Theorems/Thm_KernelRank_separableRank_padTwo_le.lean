-- Prove2me | Theorems.Thm_KernelRank_separableRank_padTwo_le
-- name    : KernelRank.separableRank_padTwo_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:04.361607+00:00
-- url     : https://prove2.me/theorems/37cf0df9-e9cb-4ec9-9a4d-c79c020a3b91
-- title:
--   Kernel Rank: separable Rank pad Two le
-- statement:
--   Restricting a `d`-variable kernel (`d ≥ 2`) to its 2-D coordinate slice cannot increase
--   separable rank.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L85-L119
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L85-L119

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.separableRank_padTwo_le {𝕜 α : Type*} [CommSemiring 𝕜] [Zero α] {d : ℕ} (hd : 2 ≤ d)
    (K : (Fin d → α) → 𝕜) :
    separableRank (fun y : Fin 2 → α => K (padTwo y)) ≤ separableRank K := by sorry
