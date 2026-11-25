-- Prove2me | Theorems.Thm_LieTrotter_norm_trotter_sub_le_commutator
-- name    : LieTrotter.norm_trotter_sub_le_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:46:26.856014+00:00
-- url     : https://prove2.me/theorems/a1e3db94-15a1-4700-9ed8-f93731c32d2f
-- title:
--   Lie Trotter: norm trotter sub le commutator
-- statement:
--   **The Lie–Trotter product formula with commutator scaling.** For `n ≥ 1`,
--   `‖(exp (A/n) · exp (B/n))ⁿ − exp (A + B)‖ ≤ ‖AB − BA‖ / (2n) · e^{‖A‖ + ‖B‖}`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L196-L243
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L196-L243

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

theorem LieTrotter.norm_trotter_sub_le_commutator (A B : 𝔸) (n : ℕ) (hn : 1 ≤ n) :
    ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      ≤ ‖A * B - B * A‖ / (2 * n) * Real.exp (‖A‖ + ‖B‖) := by sorry
