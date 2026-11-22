-- Prove2me | Theorems.Thm_Lean4LPD_total_truncation_error_product_bound
-- name    : Lean4LPD.total_truncation_error_product_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:06.347684+00:00
-- url     : https://prove2.me/theorems/0aafe0fc-5d30-45a1-af21-bc5e09b5716f
-- title:
--   Lean4 LPD: total truncation error product bound
-- statement:
--   `total_truncation_error` composed with the product estimate
--   `prod_add_one_le_factorial_exp_rpow`: the summed truncation error is at most
--   `(t/t₀)^{m+1} (e(m+1))^c ‖O‖` with `t/t₀ = decayBase Γ k_h a t`. Only the product estimate is
--   added here; the hypothesis `hstep` of `total_truncation_error` is retained unchanged, and is
--   proved from reset and layer inflow in `MultiLadder.sum_block_epsJump_le_cZero` below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L129-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L129-L157

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

theorem Lean4LPD.total_truncation_error_product_bound {S M t a G kh1 c B : ℝ} {m r : ℕ}
    (hstep : S ≤ (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
              * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
              / (Nat.factorial (m + 1) : ℝ) * M)
    (hadm : Admissible (r : ℝ) (m : ℝ) G) (hm1 : 1 ≤ (m : ℝ)) (hr5 : 5 ≤ (r : ℝ))
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh1 : 0 < kh1) (hc : 0 ≤ c)
    (ha : 0 < a) (ht : 0 ≤ t) (hM : 0 ≤ M) :
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M := by sorry
