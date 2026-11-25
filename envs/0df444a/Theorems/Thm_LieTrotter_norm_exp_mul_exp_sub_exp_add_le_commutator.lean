-- Prove2me | Theorems.Thm_LieTrotter_norm_exp_mul_exp_sub_exp_add_le_commutator
-- name    : LieTrotter.norm_exp_mul_exp_sub_exp_add_le_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:46:19.733799+00:00
-- url     : https://prove2.me/theorems/da9dd68f-9be9-5d82-93e6-800185163e26
-- title:
--   Lie Trotter: norm exp mul exp sub exp add le commutator
-- statement:
--   **The one-step bound with the commutator.**
--   `‖exp A * exp B − exp (A + B)‖ ≤ ‖AB − BA‖ / 2 · e^{‖A‖ + ‖B‖}`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L111-L170
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L111-L170

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

theorem LieTrotter.norm_exp_mul_exp_sub_exp_add_le_commutator (A B : 𝔸) :
    ‖exp A * exp B - exp (A + B)‖ ≤ ‖A * B - B * A‖ / 2 * Real.exp (‖A‖ + ‖B‖) := by sorry
