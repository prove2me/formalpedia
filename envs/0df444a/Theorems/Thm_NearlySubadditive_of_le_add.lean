-- Prove2me | Theorems.Thm_NearlySubadditive_of_le_add
-- name    : NearlySubadditive.of_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:51.996413+00:00
-- url     : https://prove2.me/theorems/83143ae8-d745-42be-8a0d-d83ff8d505f8
-- title:
--   Nearly Subadditive: of le add
-- statement:
--   Near subadditivity for all pairs above a threshold implies it on every window.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L114-L115
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L114-L115

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
variable {f g : ℕ → ℝ} {μ ν : ℝ} {N M : ℕ} {u v : ℕ → ℝ}

theorem NearlySubadditive.of_le_add (h : ∀ m n, N ≤ m → N ≤ n → u (m + n) ≤ u m + u n + f (m + n)) :
    NearlySubadditive f μ N u := by sorry
