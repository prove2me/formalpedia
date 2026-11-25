-- Prove2me | Theorems.Thm_NearlySubadditive_tendsto_witness_div
-- name    : NearlySubadditive.tendsto_witness_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:26.440933+00:00
-- url     : https://prove2.me/theorems/448f9b12-f000-48ba-863c-67d46d62a558
-- title:
--   Nearly Subadditive: tendsto witness div
-- statement:
--   If `∑ f n / n ^ 2` diverges, the witness has `u n / n → ∞`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L103-L111
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L103-L111

module
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f : ℕ → ℝ}

theorem NearlySubadditive.tendsto_witness_div (hf0 : 0 ≤ f)
    (hfs : ¬ Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) :
    Tendsto (fun n ↦ witness f n / n) atTop atTop := by sorry
