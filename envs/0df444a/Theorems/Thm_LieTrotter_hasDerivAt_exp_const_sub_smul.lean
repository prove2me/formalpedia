-- Prove2me | Theorems.Thm_LieTrotter_hasDerivAt_exp_const_sub_smul
-- name    : LieTrotter.hasDerivAt_exp_const_sub_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:46:17.610123+00:00
-- url     : https://prove2.me/theorems/0c83c4e8-4ff2-59f0-8541-b30e6973709d
-- title:
--   Lie Trotter: has Deriv At exp const sub smul
-- statement:
--   The derivative of `σ ↦ exp ((c − σ) • X)` is `-(X * exp ((c − σ) • X))`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L55-L59
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L55-L59

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
omit [NormOneClass 𝔸]

theorem LieTrotter.hasDerivAt_exp_const_sub_smul (X : 𝔸) (c σ : ℝ) :
    HasDerivAt (fun σ : ℝ => exp ((c - σ) • X)) (-(X * exp ((c - σ) • X))) σ := by sorry
