-- Prove2me | Theorems.Thm_Lean4LPD_slot_polynomial_eq_sectors
-- name    : Lean4LPD.slot_polynomial_eq_sectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:09.808343+00:00
-- url     : https://prove2.me/theorems/256c79a5-278a-4b2a-a8ad-656b6d4dbdd7
-- title:
--   Lean4 LPD: slot polynomial eq sectors
-- statement:
--   Exact reindexing by `D=m-K` in `apd:eq:total_high_weight_norm`, keeping
--   the all-ones prefactor `X^m/m!` explicit. Only the positive slot count `X` is divided out.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L197-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L197-L214

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.slot_polynomial_eq_sectors {m : ℕ} (hm : 1 ≤ m) {X R : ℝ} (hX : 0 < X) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) =
      X ^ m / (Nat.factorial m : ℝ) *
        ∑ D ∈ range m, ((m - 1).choose D : ℝ) *
          ((Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ)) * (R / X) ^ D := by sorry
