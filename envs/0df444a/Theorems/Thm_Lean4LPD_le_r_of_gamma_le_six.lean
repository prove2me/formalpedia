-- Prove2me | Theorems.Thm_Lean4LPD_le_r_of_gamma_le_six
-- name    : Lean4LPD.le_r_of_gamma_le_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:21.947971+00:00
-- url     : https://prove2.me/theorems/5153ac2c-f77e-4123-b82e-afb6ca5fb9c7
-- title:
--   Lean4 LPD: le r of gamma le six
-- statement:
--   **`Γ ≤ 6` forces `r ≥ 5`**, so under that cap `c₀ ≤ 2` is a *corollary* of `cZero_le_two`,
--   needing no new estimate. `8(m*+1)² ≤ rΓ ≤ 6r` with `m* ≥ 1` gives `r ≥ 16/3`.
--
--   Six is the physically interesting cap: the second-order formula (`Υ = 2`) on a 1D
--   nearest-neighbour chain with bare `Γ = 3` has effective count exactly 6.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L409-L412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L409-L412

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.le_r_of_gamma_le_six {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hG6 : G ≤ 6) :
    5 ≤ r := by sorry
