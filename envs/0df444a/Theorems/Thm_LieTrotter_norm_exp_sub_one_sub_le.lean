-- Prove2me | Theorems.Thm_LieTrotter_norm_exp_sub_one_sub_le
-- name    : LieTrotter.norm_exp_sub_one_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:36:58.207376+00:00
-- url     : https://prove2.me/theorems/7c38fea5-fb3a-46c4-b38c-c35b9ef677ee
-- title:
--   Lie Trotter: norm exp sub one sub le
-- statement:
--   **The quantitative second-order remainder**, Banach-algebra form:
--   `‖exp X − 1 − X‖ ≤ ‖X‖² · e^{‖X‖}`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L84-L133
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean#L84-L133

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
set_option maxHeartbeats 800000

theorem LieTrotter.norm_exp_sub_one_sub_le (X : 𝔸) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by sorry
