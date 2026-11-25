-- Prove2me | Theorems.Thm_LieTrotter_trotter_product
-- name    : LieTrotter.trotter_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:36:59.417739+00:00
-- url     : https://prove2.me/theorems/baf163a8-598b-4c3e-893d-f9a752e083c8
-- title:
--   Lie Trotter: trotter product
-- statement:
--   **The Lie–Trotter product formula in a Banach algebra**: for any `A, B`,
--   `(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L354-L369
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L354-L369

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

theorem LieTrotter.trotter_product (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n)
      Filter.atTop (nhds (exp (A + B))) := by sorry
