-- Prove2me | Theorems.Thm_LieTrotter_trotter_eq_of_commute
-- name    : LieTrotter.trotter_eq_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:53:48.778186+00:00
-- url     : https://prove2.me/theorems/5f2e09ed-3ae3-4b88-8cfa-528eabe94456
-- title:
--   Lie Trotter: trotter eq of commute
-- statement:
--   When `A` and `B` commute, the product formula is exact at every step: the error bound
--   vanishes.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L247-L251
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L247-L251

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

theorem LieTrotter.trotter_eq_of_commute {A B : 𝔸} (h : Commute A B) (n : ℕ) (hn : 1 ≤ n) :
    (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n = exp (A + B) := by sorry
