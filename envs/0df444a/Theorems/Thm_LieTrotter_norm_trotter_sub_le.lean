-- Prove2me | Theorems.Thm_LieTrotter_norm_trotter_sub_le
-- name    : LieTrotter.norm_trotter_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:36:57.785618+00:00
-- url     : https://prove2.me/theorems/9f01c797-2481-48f4-94d2-67fc7da3831e
-- title:
--   Lie Trotter: norm trotter sub le
-- statement:
--   **The explicit rate.** For `n ≥ 1`,
--   `‖(exp (A/n) · exp (B/n))ⁿ − exp (A + B)‖ ≤ n⁻¹ · s²(3 + s)e^{2s}` with `s = ‖A‖ + ‖B‖`.
--   The one-step defect is `O(1/n²)`, and the telescoping costs `n · (e^{s/n})ⁿ = n e^s`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L268-L350
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L268-L350

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

theorem LieTrotter.norm_trotter_sub_le (A B : 𝔸) (n : ℕ) (hn : 1 ≤ n) :
    ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      ≤ (n : ℝ)⁻¹ * ((‖A‖ + ‖B‖) ^ 2 * (3 + (‖A‖ + ‖B‖)) * Real.exp (2 * (‖A‖ + ‖B‖))) := by sorry
