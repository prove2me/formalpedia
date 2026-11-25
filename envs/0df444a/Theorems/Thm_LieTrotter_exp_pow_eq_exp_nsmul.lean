-- Prove2me | Theorems.Thm_LieTrotter_exp_pow_eq_exp_nsmul
-- name    : LieTrotter.exp_pow_eq_exp_nsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:36:54.975449+00:00
-- url     : https://prove2.me/theorems/bd6a75ab-935b-451a-b982-80750a1444df
-- title:
--   Lie Trotter: exp pow eq exp nsmul
-- statement:
--   `exp x ^ n = exp (n • x)`, by induction from `exp_add_of_commute`. (Mathlib's `exp_nsmul`
--   needs a `ℚ`-algebra instance, which instance search does not find for a general real Banach
--   algebra; it could be supplied by restricting scalars from `ℝ` to `ℚ`.)
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L253-L262
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L253-L262

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
omit [NormOneClass 𝔸]

theorem LieTrotter.exp_pow_eq_exp_nsmul (x : 𝔸) (n : ℕ) : exp x ^ n = exp (n • x) := by sorry
