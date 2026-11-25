-- Prove2me | Theorems.Thm_NearlySubadditive_lim_le_div
-- name    : NearlySubadditive.lim_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:58.28552+00:00
-- url     : https://prove2.me/theorems/9c9042d8-f691-5b4f-bd2f-bad95e8fd239
-- title:
--   Nearly Subadditive: lim le div
-- statement:
--   Every `u k / k` with `N ≤ k` and `k ≠ 0` bounds `NearlySubadditive.lim N u` from above.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L366-L369
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L366-L369

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_Fekete_Window
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}

theorem NearlySubadditive.lim_le_div (hbdd : BddBelow (range fun n ↦ u n / n)) {k : ℕ} (hN : N ≤ k) (hk : k ≠ 0) :
    NearlySubadditive.lim N u ≤ u k / k := by sorry
