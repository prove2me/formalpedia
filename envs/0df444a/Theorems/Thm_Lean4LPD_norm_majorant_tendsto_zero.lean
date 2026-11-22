-- Prove2me | Theorems.Thm_Lean4LPD_norm_majorant_tendsto_zero
-- name    : Lean4LPD.norm_majorant_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:13.353079+00:00
-- url     : https://prove2.me/theorems/1022796d-9d71-42e2-9a86-5b835c712fe9
-- title:
--   Lean4 LPD: norm majorant tendsto zero
-- statement:
--   The analytic decay behind `apd:thm:truncation_threshold_entangled`, applied to the norm-level
--   majorant of `total_truncation_error_product_bound`: for `0 ≤ q < 1` and all real `c, M`,
--   `q^(m+1) (e(m+1))^c M → 0` as `m → ∞`. The exponential decay of `q^(m+1)` dominates the
--   polynomial factor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L62-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L62-L83

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology

theorem Lean4LPD.norm_majorant_tendsto_zero {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c M : ℝ) :
    Tendsto (fun m : ℕ => q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
      atTop (𝓝 0) := by sorry
