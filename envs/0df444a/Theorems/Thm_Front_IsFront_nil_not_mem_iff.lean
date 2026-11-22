-- Prove2me | Theorems.Thm_Front_IsFront_nil_not_mem_iff
-- name    : Front.IsFront.nil_not_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:41.386833+00:00
-- url     : https://prove2.me/theorems/df5773fe-dc88-4c96-a732-012f34bf6850
-- title:
--   Is Front: nil not mem iff
-- statement:
--   A front is *nontrivial* (`[] ∉ F`) iff it is not the trivial front `{[]}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L117-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L117-L124

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

theorem Front.IsFront.nil_not_mem_iff (hF : IsFront F M) : [] ∉ F ↔ F ≠ {[]} := by sorry
