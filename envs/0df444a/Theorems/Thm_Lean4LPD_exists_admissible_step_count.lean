-- Prove2me | Theorems.Thm_Lean4LPD_exists_admissible_step_count
-- name    : Lean4LPD.exists_admissible_step_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:56.304591+00:00
-- url     : https://prove2.me/theorems/17b31d79-b5f6-4490-af65-a992c60d4d75
-- title:
--   Lean4 LPD: exists admissible step count
-- statement:
--   Numerical step counts can be chosen after the rung: an Archimedean helper for the conditions
--   of `apd:eq:multijump_factor`. The two real lower bounds `B₁`, `B₂` may encode the paper's
--   finite-step conditions `r ≥ 8(m*+1)²/Γ` and `r ≥ 8e²·w₂·αt`; satisfying them does not construct
--   or update any gate-angle family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L148-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L148-L156

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

theorem Lean4LPD.exists_admissible_step_count (m : ℕ) (B₁ B₂ : ℝ) :
    ∃ r : ℕ, 5 ≤ r ∧ m ≤ r ∧ B₁ ≤ (r : ℝ) ∧ B₂ ≤ (r : ℝ) := by sorry
