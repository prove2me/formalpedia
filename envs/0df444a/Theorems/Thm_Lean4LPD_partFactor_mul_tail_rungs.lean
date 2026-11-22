-- Prove2me | Theorems.Thm_Lean4LPD_partFactor_mul_tail_rungs
-- name    : Lean4LPD.partFactor_mul_tail_rungs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:48.498071+00:00
-- url     : https://prove2.me/theorems/4982b11c-7164-429c-8dd9-b7b6b6a14ca7
-- title:
--   Lean4 LPD: part Factor mul tail rungs
-- statement:
--   Multiplying the part factor by its rung product gives the `j`-jump numerator
--   `w_{m+j}^j / j!`. This is the division-free-in-angle version of `apd:eq:part_factor`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L99-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L99-L113

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.partFactor_mul_tail_rungs {c : ℝ} (hc : 0 ≤ c) (kh1 : ℝ)
    {j m : ℕ} (hjm : j ≤ m) :
    partFactor j ((m : ℝ) + c) * (∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
      = rungW kh1 c (m + j) ^ j / (Nat.factorial j : ℝ) := by sorry
