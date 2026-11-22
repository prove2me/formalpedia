-- Prove2me | Theorems.Thm_Lean4LPD_chain_slot_sum_le_exp
-- name    : Lean4LPD.chain_slot_sum_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:05.324417+00:00
-- url     : https://prove2.me/theorems/de14c867-449b-45bc-98a6-bc0a39f5eee2
-- title:
--   Lean4 LPD: chain slot sum le exp
-- statement:
--   Combine the proved local-ratio chain bound with the full `D`-sector estimate of
--   `apd:eq:total_high_weight_norm`. The entry inflation `C` is charged exactly once;
--   the desired chain sum is a conclusion, not one of the local coefficient hypotheses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L231-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L231-L255

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

theorem Lean4LPD.chain_slot_sum_le_exp {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ} {C R X : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (heps : ∀ j m, 0 ≤ eps j m) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hW : 0 ≤ W m) (hX : 0 < X)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      chain eps E (k + 1) m) ≤
      C * W m * X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by sorry
