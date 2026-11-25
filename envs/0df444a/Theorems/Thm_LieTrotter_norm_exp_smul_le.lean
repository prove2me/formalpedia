-- Prove2me | Theorems.Thm_LieTrotter_norm_exp_smul_le
-- name    : LieTrotter.norm_exp_smul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:46:21.134106+00:00
-- url     : https://prove2.me/theorems/d45ac80c-d38a-4e7a-a940-1e3260fdc958
-- title:
--   Lie Trotter: norm exp smul le
-- statement:
--   `‖exp (t • X)‖ ≤ e^{t ‖X‖}` for `t ≥ 0`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L48-L51
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L48-L51

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

theorem LieTrotter.norm_exp_smul_le (X : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • X)‖ ≤ Real.exp (t * ‖X‖) := by sorry
