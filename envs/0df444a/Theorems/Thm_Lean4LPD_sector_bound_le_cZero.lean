-- Prove2me | Theorems.Thm_Lean4LPD_sector_bound_le_cZero
-- name    : Lean4LPD.sector_bound_le_cZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:11.185399+00:00
-- url     : https://prove2.me/theorems/017f12b0-9625-4d83-99dc-9e1fe851217f
-- title:
--   Lean4 LPD: sector bound le c Zero
-- statement:
--   The scalar passage from the sharper sector denominator `(r+1)Γ` to the `c₀` shape of
--   `apd:eq:total_high_weight_norm` and `apd:eq:c0`. `A` stands for the paper's product `αt`; only
--   the angle bound `a ≤ A/r` is used.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L301-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L301-L341

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

theorem Lean4LPD.sector_bound_le_cZero {r G B a A P M : ℝ}
    (hr : 0 < r) (hG : 0 < G) (hB : 0 ≤ B) (ha0 : 0 ≤ a) (hA : 0 ≤ A)
    (ha : a ≤ A / r) (hP : 0 ≤ P) (hM : 0 ≤ M) (m : ℕ) :
    M * ((1 + B) * (a ^ (m + 1) * P) * ((r + 1) * G) ^ (m + 1) /
      (Nat.factorial (m + 1) : ℝ) *
      Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G))) ≤
      (cZero r (m : ℝ) G B * G * A) ^ (m + 1) * P /
        (Nat.factorial (m + 1) : ℝ) * M := by sorry
