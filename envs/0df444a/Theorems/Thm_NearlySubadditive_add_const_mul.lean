-- Prove2me | Theorems.Thm_NearlySubadditive_add_const_mul
-- name    : NearlySubadditive.add_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:16.402914+00:00
-- url     : https://prove2.me/theorems/f87a0bb1-0fd2-5ddf-93e6-3617256b12dd
-- title:
--   Nearly Subadditive: add const mul
-- statement:
--   Adding a linear term `c * n` preserves near subadditivity.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L103-L106
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L103-L106

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

theorem NearlySubadditive.add_const_mul (h : NearlySubadditive f μ N u) (c : ℝ) :
    NearlySubadditive f μ N fun n ↦ u n + c * n := by sorry
