-- Prove2me | Theorems.Thm_NearlySubadditive_const_mul
-- name    : NearlySubadditive.const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:36.433194+00:00
-- url     : https://prove2.me/theorems/55f28f22-c27b-4361-9c6d-220d65156c14
-- title:
--   Nearly Subadditive: const mul
-- statement:
--   Scaling by `c ≥ 0` scales the error.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L109-L111
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L109-L111

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

theorem NearlySubadditive.const_mul (h : NearlySubadditive f μ N u) {c : ℝ} (hc : 0 ≤ c) :
    NearlySubadditive (fun n ↦ c * f n) μ N fun n ↦ c * u n := by sorry
