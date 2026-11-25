-- Prove2me | Theorems.Thm_LieTrotter_norm_pow_sub_pow_le_of_norm_le
-- name    : LieTrotter.norm_pow_sub_pow_le_of_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:36:56.856552+00:00
-- url     : https://prove2.me/theorems/a2c0707f-85f1-409e-a5c7-94f7b1bbc041
-- title:
--   Lie Trotter: norm pow sub pow le of norm le
-- statement:
--   **Growth-controlled telescoping**: for `‖S‖, ‖T‖ ≤ C` with `1 ≤ C`,
--   `‖Sⁿ − Tⁿ‖ ≤ n · Cⁿ · ‖S − T‖`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L211-L247
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L211-L247

module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing
public import Definitions.Def_LieTrotter_Basic
set_option autoImplicit false
@[expose] public section
public section
open NormedSpace
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]
omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem LieTrotter.norm_pow_sub_pow_le_of_norm_le {S T : 𝔸} {C : ℝ} (hC : 1 ≤ C)
    (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C) (n : ℕ) :
    ‖S ^ n - T ^ n‖ ≤ n * C ^ n * ‖S - T‖ := by sorry
