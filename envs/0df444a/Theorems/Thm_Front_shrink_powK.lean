-- Prove2me | Theorems.Thm_Front_shrink_powK
-- name    : Front.shrink_powK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:45.03024+00:00
-- url     : https://prove2.me/theorems/e12aa72a-7ec7-40ea-9cd8-023d7c93d200
-- title:
--   Front: shrink pow K
-- statement:
--   The restriction of the uniform front `[M]^k` to an infinite subset `M ∘ e` is the uniform
--   front `[M ∘ e]^k` on that subset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L117-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L117-L126

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

theorem Front.shrink_powK {e : ℕ → ℕ} (k : ℕ) :
    shrink (powK M k) (M ∘ e) = powK (M ∘ e) k := by sorry
