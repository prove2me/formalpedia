-- Prove2me | Theorems.Thm_NearlySubadditive_tendsto_div_atBot
-- name    : NearlySubadditive.tendsto_div_atBot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:48.59566+00:00
-- url     : https://prove2.me/theorems/47f1be34-3aab-5ccf-8198-1f8dc44b8f8a
-- title:
--   Nearly Subadditive: tendsto div at Bot
-- statement:
--   If `u` is subadditive on a window and `u n / n` is not bounded below, then `u n / n → -∞`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L353-L356
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L353-L356

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

theorem NearlySubadditive.tendsto_div_atBot (hμ : 1 < μ) (h : NearlySubadditive 0 μ N u)
    (hbdd : ¬ BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot := by sorry
