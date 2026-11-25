-- Prove2me | Theorems.Thm_NearlySubadditive_witness_le_add
-- name    : NearlySubadditive.witness_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:24.978421+00:00
-- url     : https://prove2.me/theorems/02454d62-7d06-4983-a394-e8e3c20b6988
-- title:
--   Nearly Subadditive: witness le add
-- statement:
--   **Füredi–Ruzsa, Claim 7.** The witness is nearly `f`-subadditive for all pairs.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L68-L100
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L68-L100

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

theorem NearlySubadditive.witness_le_add (hf0 : 0 ≤ f) (hf : Monotone f) (m n : ℕ) :
    witness f (m + n) ≤ witness f m + witness f n + f (m + n) := by sorry
