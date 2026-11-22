-- Prove2me | Theorems.Thm_Lean4LPD_cZero_extremal_isotone_gamma
-- name    : Lean4LPD.cZero_extremal_isotone_gamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:20.233166+00:00
-- url     : https://prove2.me/theorems/3f77478c-042b-442b-a4f8-32d7126ac29c
-- title:
--   Lean4 LPD: c Zero extremal isotone gamma
-- statement:
--   **Along the admissible boundary, `c₀` is isotone in `Γ`**, in contrast to
--   `cZero_antitone_gamma` at fixed `r`; this is the direction relevant to a cap on `Γ`.
--
--   Both points below are admissible with `rΓ = 8(m*+1)² = 32` exactly, so both are *extremal* for their
--   cap, and the value **rises** with `Γ`:
--
--     `c₀(32/6, 1, 6, 1) ≈ 1.9329  <  c₀(32/7, 1, 7, 1) ≈ 1.9838`.
--
--   The mechanism is `r`'s floor, not the exponential: `Admissible` forces `r ≥ 32/Γ`, so raising `Γ`
--   *lowers* the smallest admissible `r` and `(r+1)/r → 2`. At fixed `r` the exponential does fall —
--   that is `cZero_antitone_gamma` — so the two monotonicity statements have opposite signs and differ
--   in what is held fixed.
--
--   The proof is exact rational arithmetic, which is the cleanest evidence that the exponential is not
--   what is moving: at both points `rΓ = 32` and `m* = 1`, so `exp (9/4·(m*+1)/(rΓ)) = exp (9/64)` and
--   `(1+B)^{1/(m*+1)} = √2` are *literally the same factors* on each side, and the comparison reduces to
--   `(r+1)/r`: `19/16 < 39/32`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L496-L508
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L496-L508

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_extremal_isotone_gamma :
    Admissible (32 / 6) 1 6 ∧ Admissible (32 / 7) 1 7 ∧
      cZero (32 / 6) 1 6 1 < cZero (32 / 7) 1 7 1 := by sorry
