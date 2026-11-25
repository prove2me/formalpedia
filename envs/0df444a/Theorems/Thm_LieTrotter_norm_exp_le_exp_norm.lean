-- Prove2me | Theorems.Thm_LieTrotter_norm_exp_le_exp_norm
-- name    : LieTrotter.norm_exp_le_exp_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:36:50.482141+00:00
-- url     : https://prove2.me/theorems/1b77be5d-6d70-4733-877e-49505f83a167
-- title:
--   Lie Trotter: norm exp le exp norm
-- statement:
--   **The exponential norm bound**: `‖exp X‖ ≤ e^{‖X‖}` (termwise domination
--   of the exponential series).
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L54-L78
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L54-L78

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
set_option maxHeartbeats 800000

theorem LieTrotter.norm_exp_le_exp_norm (X : 𝔸) : ‖exp X‖ ≤ Real.exp ‖X‖ := by sorry
