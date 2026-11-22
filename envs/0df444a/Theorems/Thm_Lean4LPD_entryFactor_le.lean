-- Prove2me | Theorems.Thm_Lean4LPD_entryFactor_le
-- name    : Lean4LPD.entryFactor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:24.856341+00:00
-- url     : https://prove2.me/theorems/ef043aca-f002-4eb8-acfa-576320ce4b69
-- title:
--   Lean4 LPD: entry Factor le
-- statement:
--   **The entry-factor bound, affine form** (`apd:eq:entry_bound`):
--
--     `E_ν ≤ ε_ν^{(ν)} · (1 + 2β)`  for `β ≤ 1/2`.
--
--   The constant `2` is stronger than the paper's statement, which has `4e ≈ 10.87` in its place.
--   Since `1 + 2β ≤ 1 + 4eβ` for `β ≥ 0` (`one_add_two_mul_le_source`), the bound with `(1 + 4eβ)`
--   follows, so every downstream use of that factor remains valid.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L274-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L274-L294

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.entryFactor_le {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {nu : ℕ} (hnu : 1 ≤ nu) (hb : betaOf kh1 c a ≤ 1 / 2) :
    entryFactor kh1 c a nu ≤ epsJump kh1 c a nu nu * (1 + 2 * betaOf kh1 c a) := by sorry
