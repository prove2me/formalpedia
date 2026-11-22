-- Prove2me | Theorems.Thm_Front_IsFront_shrink_rank_le
-- name    : Front.IsFront.shrink_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:41.218835+00:00
-- url     : https://prove2.me/theorems/29cf49bb-823d-439e-b634-57d264cde5ea
-- title:
--   Is Front: shrink rank le
-- statement:
--   **Restriction does not increase rank.** The restriction of a front to an infinite subset has
--   rank at most that of the front.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L135-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L135-L146

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}

theorem Front.IsFront.shrink_rank_le (hF : IsFront F M) {E : ℕ → ℕ} (hE : StrictMono E) :
    (shrink_isFront hF hE).rank ≤ hF.rank := by sorry
