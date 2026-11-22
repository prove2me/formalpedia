-- Prove2me | Theorems.Thm_Lean4LPD_prod_add_one_le_factorial_exp_rpow
-- name    : Lean4LPD.prod_add_one_le_factorial_exp_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:12.316523+00:00
-- url     : https://prove2.me/theorems/d1c0f015-db55-4c03-b1f8-3fbad3a5a0cc
-- title:
--   Lean4 LPD: prod add one le factorial exp rpow
-- statement:
--   The product estimate for `apd:eq:total_high_weight_norm`: for `c ≥ 0` and `n ≥ 1`,
--   `∏_{i=1}^n (i+c) ≤ n! (e n)^c`. By `prod_rungW_eq` the left-hand side is the rung product
--   `∏_{j=2}^{n+1} w_j` up to the factor `(k_h-1)^n`. The proof writes the product as
--   `n! ∏_{i=1}^n (1 + c/i)`, bounds it by `n! exp(c H_n)`, and uses `H_n ≤ 1 + log n`.
--
--   The hypothesis `n ≥ 1` cannot be dropped: at `n = 0` the empty product is `1`, while
--   `(e · 0)^c = 0` for every `c > 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L67-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L67-L97

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

theorem Lean4LPD.prod_add_one_le_factorial_exp_rpow {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) ≤
      (Nat.factorial n : ℝ) * (Real.exp 1 * (n : ℝ)) ^ c := by sorry
