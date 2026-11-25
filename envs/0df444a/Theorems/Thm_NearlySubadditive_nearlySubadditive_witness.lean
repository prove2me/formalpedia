-- Prove2me | Theorems.Thm_NearlySubadditive_nearlySubadditive_witness
-- name    : NearlySubadditive.nearlySubadditive_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:18.356492+00:00
-- url     : https://prove2.me/theorems/118d3c4c-ebb2-541b-8516-340202f1b284
-- title:
--   Nearly Subadditive: nearly Subadditive witness
-- statement:
--   The witness is nearly `f`-subadditive on every window.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L114-L116
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L114-L116

module
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f : ℕ → ℝ}

theorem NearlySubadditive.nearlySubadditive_witness (hf0 : 0 ≤ f) (hf : Monotone f) (μ : ℝ) (N : ℕ) :
    NearlySubadditive f μ N (witness f) := by sorry
