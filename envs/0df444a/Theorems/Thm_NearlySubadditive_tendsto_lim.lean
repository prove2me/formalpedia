-- Prove2me | Theorems.Thm_NearlySubadditive_tendsto_lim
-- name    : NearlySubadditive.tendsto_lim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:56.693443+00:00
-- url     : https://prove2.me/theorems/57f89aee-d8ca-4d1d-afd3-9b133befaae3
-- title:
--   Nearly Subadditive: tendsto lim
-- statement:
--   If `u` is subadditive on a window and `u n / n` is bounded below, then `u n / n` converges to
--   `⨅ k ≥ max N 1, u k / k`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L373-L400
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L373-L400

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

theorem NearlySubadditive.tendsto_lim (hμ : 1 < μ) (h : NearlySubadditive 0 μ N u)
    (hbdd : BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop (𝓝 (NearlySubadditive.lim N u)) := by sorry
