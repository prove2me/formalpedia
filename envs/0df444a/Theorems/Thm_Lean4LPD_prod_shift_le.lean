-- Prove2me | Theorems.Thm_Lean4LPD_prod_shift_le
-- name    : Lean4LPD.prod_shift_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:46.318222+00:00
-- url     : https://prove2.me/theorems/855eb705-e674-490c-922b-f2511ec6f9cc
-- title:
--   Lean4 LPD: prod shift le
-- statement:
--   The exact product is dominated by the shifted one: `∏_{i=1}^{n}(i+c) ≤ ∏_{i=2}^{n+1}(i+c)`
--   for `c ≥ 0`, termwise. Hence a bound proved with the exact product of `prod_rungW_eq` implies the
--   same bound with the shifted product, the form displayed in the paper.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L181-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L181-L186

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.prod_shift_le {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) ≤ ∏ i ∈ range n, ((i : ℝ) + 2 + c) := by sorry
