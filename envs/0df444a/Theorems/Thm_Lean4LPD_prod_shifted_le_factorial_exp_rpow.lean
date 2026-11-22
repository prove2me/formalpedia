-- Prove2me | Theorems.Thm_Lean4LPD_prod_shifted_le_factorial_exp_rpow
-- name    : Lean4LPD.prod_shifted_le_factorial_exp_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:34.06174+00:00
-- url     : https://prove2.me/theorems/23d919e6-dc95-4210-be0e-dc0c2612f3f7
-- title:
--   Lean4 LPD: prod shifted le factorial exp rpow
-- statement:
--   The product estimate for `apd:eq:total_high_weight_norm` in shifted indexing:
--   `∏_{j=2}^{n+1} (j+c) ≤ (n+1)! (e(n+1))^c` for `c ≥ 0` and every `n`. Since `1 + c ≥ 1`, the
--   shifted product over `n` factors is at most the unshifted product over `n + 1` factors, so this
--   follows from `prod_add_one_le_factorial_exp_rpow` at `n + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L103-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L103-L122

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

theorem Lean4LPD.prod_shifted_le_factorial_exp_rpow {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∏ i ∈ range n, ((i : ℝ) + 2 + c) ≤
      (Nat.factorial (n + 1) : ℝ) * (Real.exp 1 * ((n : ℝ) + 1)) ^ c := by sorry
