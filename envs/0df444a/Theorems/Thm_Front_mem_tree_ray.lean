-- Prove2me | Theorems.Thm_Front_mem_tree_ray
-- name    : Front.mem_tree_ray
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:49.032635+00:00
-- url     : https://prove2.me/theorems/8ea4a691-96c7-4896-a315-fb7a28d46798
-- title:
--   Front: mem tree ray
-- statement:
--   The tree of the ray at `a` is `tree F` above `[a]`, stripped of the leading `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L240-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L240-L246

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

theorem Front.mem_tree_ray {a : ℕ} {t : List ℕ} : t ∈ tree (ray F a) ↔ a :: t ∈ tree F := by sorry
