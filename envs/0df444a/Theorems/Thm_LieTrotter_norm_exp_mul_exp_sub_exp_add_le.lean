-- Prove2me | Theorems.Thm_LieTrotter_norm_exp_mul_exp_sub_exp_add_le
-- name    : LieTrotter.norm_exp_mul_exp_sub_exp_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:37:02.761437+00:00
-- url     : https://prove2.me/theorems/8187063c-3ee6-4f64-8763-6fadf6b1572b
-- title:
--   Lie Trotter: norm exp mul exp sub exp add le
-- statement:
--   **The one-step defect**, for any `X, Y`, with no commutativity assumption:
--   `‖exp X · exp Y − exp (X+Y)‖ ≤ (‖X‖+‖Y‖)²·(3+‖X‖+‖Y‖)·e^{‖X‖+‖Y‖}`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L137-L206
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L137-L206

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

theorem LieTrotter.norm_exp_mul_exp_sub_exp_add_le (X Y : 𝔸) :
    ‖exp X * exp Y - exp (X + Y)‖
      ≤ (‖X‖ + ‖Y‖) ^ 2 * (3 + (‖X‖ + ‖Y‖)) * Real.exp (‖X‖ + ‖Y‖) := by sorry
