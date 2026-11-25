-- Prove2me | Theorems.Thm_NearlySubadditive_exists_tendsto_div_of_summable
-- name    : NearlySubadditive.exists_tendsto_div_of_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:03.813543+00:00
-- url     : https://prove2.me/theorems/c25fa023-a4a8-5009-b9d4-1fa222a4c14c
-- title:
--   Nearly Subadditive: exists tendsto div of summable
-- statement:
--   **De Bruijn–Erdős**, bounded below case. If `u (m + n) ≤ u m + u n + f (m + n)` on the window
--   `N ≤ m ≤ n ≤ μ * m` with `μ > 1`, where `f` is monotone and `∑ f n / n ^ 2 < ∞`, and `u n / n` is
--   bounded below, then `u n / n` converges to a real limit.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L178-L183
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L178-L183

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

theorem NearlySubadditive.exists_tendsto_div_of_summable (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    (hbdd : BddBelow (Set.range fun n ↦ u n / n)) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) := by sorry
