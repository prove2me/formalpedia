-- Prove2me | Theorems.Thm_NearlySubadditive_tendsto_atBot_or_exists_tendsto
-- name    : NearlySubadditive.tendsto_atBot_or_exists_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:52.227849+00:00
-- url     : https://prove2.me/theorems/79429d3e-2f42-46bf-88a7-53e7f263a377
-- title:
--   Nearly Subadditive: tendsto at Bot or exists tendsto
-- statement:
--   **Füredi–Ruzsa, Theorem 2.** If `u` is subadditive on the window `N ≤ m ≤ n ≤ μ * m` for some
--   `μ > 1`, then `u n / n` tends either to `-∞` or to a real limit.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L278-L350
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean#L278-L350

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

theorem NearlySubadditive.tendsto_atBot_or_exists_tendsto (hμ : 1 < μ) (h : NearlySubadditive 0 μ N u) :
    Tendsto (fun n ↦ u n / n) atTop atBot ∨ ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) := by sorry
