-- Prove2me | Theorems.Thm_NearlySubadditive_mono_error
-- name    : NearlySubadditive.mono_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:04.589521+00:00
-- url     : https://prove2.me/theorems/563aaf2c-9eda-457b-9cb9-de47ecb95cb6
-- title:
--   Nearly Subadditive: mono error
-- statement:
--   The Nearly Subadditive construction uses the mono error property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L85-L86
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L85-L86

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

theorem NearlySubadditive.mono_error (h : NearlySubadditive f μ N u) (hfg : f ≤ g) : NearlySubadditive g μ N u := by sorry
