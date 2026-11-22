-- Prove2me | Theorems.Thm_Lean4LPD_partFactor_antitone
-- name    : Lean4LPD.partFactor_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:18.477674+00:00
-- url     : https://prove2.me/theorems/3b03ea22-3389-4d31-8d6f-14bf8ac40119
-- title:
--   Lean4 LPD: part Factor antitone
-- statement:
--   **The one monotonicity.** `partFactor j` is antitone on `[j, ∞)`. This is monotonicity in the
--   boundary `σ` and in `c` at once, since `ρ` depends on them only through `s = σ + c`; it is what
--   places the maximum at `σ = j`, `c = 0`. The proof is termwise: with `s' = s + d`, `d ≥ 0`, the
--   `i`-th factor comparison is `d · (i − 2(j−1)) ≤ 0`, which holds because `i < j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L79-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L79-L107

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.partFactor_antitone {j : ℕ} {s s' : ℝ} (hj : 1 ≤ j) (hs : (j : ℝ) ≤ s) (hss : s ≤ s') :
    partFactor j s' ≤ partFactor j s := by sorry
