-- Prove2me | Theorems.Thm_Front_IsFront_ray_rank_lt
-- name    : Front.IsFront.ray_rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:39.914948+00:00
-- url     : https://prove2.me/theorems/cc678489-7799-4427-84b8-e167338a5a6f
-- title:
--   Is Front: ray rank lt
-- statement:
--   **The ray strictly lowers the rank.** For a nontrivial front and `n ∈ M`, the front
--   `F after n` has rank strictly below that of `F`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L250-L268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L250-L268

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
variable {M : ℕ → ℕ}
open Front
variable {F : Set (List ℕ)}

theorem Front.IsFront.ray_rank_lt (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : (hF.ray_isFront_mem h0 hn).rank < hF.rank := by sorry
