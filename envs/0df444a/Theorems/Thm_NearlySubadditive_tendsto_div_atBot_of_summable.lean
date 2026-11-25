-- Prove2me | Theorems.Thm_NearlySubadditive_tendsto_div_atBot_of_summable
-- name    : NearlySubadditive.tendsto_div_atBot_of_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:07.131045+00:00
-- url     : https://prove2.me/theorems/368cb91e-16c6-5e2a-92d7-5098b7e48853
-- title:
--   Nearly Subadditive: tendsto div at Bot of summable
-- statement:
--   **De Bruijn–Erdős**, unbounded case. Under the hypotheses of
--   `NearlySubadditive.exists_tendsto_div_of_summable`, if `u n / n` is not bounded below, then
--   `u n / n → -∞`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L188-L193
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L188-L193

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

theorem NearlySubadditive.tendsto_div_atBot_of_summable (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    (hbdd : ¬ BddBelow (Set.range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot := by sorry
