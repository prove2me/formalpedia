-- Prove2me | Theorems.Thm_NearlySubadditive_tendsto_atBot_or_exists_tendsto_of_summable
-- name    : NearlySubadditive.tendsto_atBot_or_exists_tendsto_of_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:26.951776+00:00
-- url     : https://prove2.me/theorems/91b0b8b8-d13b-5c3e-900b-2eb1ed4a8956
-- title:
--   Nearly Subadditive: tendsto at Bot or exists tendsto of summable
-- statement:
--   **De Bruijn–Erdős, Füredi–Ruzsa.** If `u (m + n) ≤ u m + u n + f (m + n)` on the window
--   `N ≤ m ≤ n ≤ μ * m` with `μ > 1`, where `f` is monotone and `∑ f n / n ^ 2 < ∞`, then
--   `u n / n` tends either to `-∞` or to a real limit.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L115-L173
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L115-L173

module
public import Definitions.Def_Fekete_Window
public import Mathlib.Analysis.PSeries
public import Definitions.Def_Fekete_DeBruijnErdos
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f u : ℕ → ℝ} {μ : ℝ} {N : ℕ}

theorem NearlySubadditive.tendsto_atBot_or_exists_tendsto_of_summable (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) :
    Tendsto (fun n ↦ u n / n) atTop atBot ∨ ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) := by sorry
