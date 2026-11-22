-- Prove2me | Theorems.Thm_Lean4LPD_cZero_antitone_gamma
-- name    : Lean4LPD.cZero_antitone_gamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:05.518709+00:00
-- url     : https://prove2.me/theorems/31d18593-3d50-4b58-b0ac-f62e564b40f6
-- title:
--   Lean4 LPD: c Zero antitone gamma
-- statement:
--   **`c₀` is antitone in `Γ` at fixed `r`.** `G` enters `cZero` only through
--   `exp (9/4·(m+1)/(r·G))`, in the denominator, so raising `Γ` lowers `c₀`.
--
--   Stated at fixed `r` deliberately: over the admissible set `r` is *not* free to stay fixed, since its
--   lower bound `8(m*+1)²/Γ` falls as `Γ` rises, and there the supremum runs the other way.
--
--   `cZero_extremal_isotone_gamma` is the statement along the admissible boundary; the two differ in
--   what is held fixed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L367-L380
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L367-L380

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_antitone_gamma {r m B G G' : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hG : 0 < G) (hGG' : G ≤ G') : cZero r m G' B ≤ cZero r m G B := by sorry
