-- Prove2me | Theorems.Thm_NearlySubadditive_add
-- name    : NearlySubadditive.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:16.434605+00:00
-- url     : https://prove2.me/theorems/ab745936-dadb-52a8-ab32-1d7ca2d6b30d
-- title:
--   Nearly Subadditive: add
-- statement:
--   The sum of two nearly subadditive sequences is nearly subadditive, with the sum of the
--   errors.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L97-L100
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L97-L100

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

theorem NearlySubadditive.add (h : NearlySubadditive f μ N u) (h' : NearlySubadditive g μ N v) :
    NearlySubadditive (f + g) μ N (u + v) := by sorry
