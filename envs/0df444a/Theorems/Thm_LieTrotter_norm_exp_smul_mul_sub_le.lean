-- Prove2me | Theorems.Thm_LieTrotter_norm_exp_smul_mul_sub_le
-- name    : LieTrotter.norm_exp_smul_mul_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:46:29.080383+00:00
-- url     : https://prove2.me/theorems/e136b9e6-8346-474c-bd7e-f1bc8b1ea484
-- title:
--   Lie Trotter: norm exp smul mul sub le
-- statement:
--   **The commutator with an exponential.** For `t ≥ 0`,
--   `‖exp (t • A) * B − B * exp (t • A)‖ ≤ t ‖AB − BA‖ e^{t ‖A‖}`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L71-L107
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L71-L107

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator
set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem LieTrotter.norm_exp_smul_mul_sub_le (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A) * B - B * exp (t • A)‖ ≤ t * ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by sorry
