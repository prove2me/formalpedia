-- Prove2me | Theorems.Thm_LieTrotter_norm_pow_succ_sub_pow_succ_le
-- name    : LieTrotter.norm_pow_succ_sub_pow_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:46:25.21117+00:00
-- url     : https://prove2.me/theorems/c32aaaf4-396f-4d4a-bef6-6f36cd68aecc
-- title:
--   Lie Trotter: norm pow succ sub pow succ le
-- statement:
--   **Telescoping**: for `‖S‖, ‖T‖ ≤ C`, `‖Sⁿ⁺¹ − Tⁿ⁺¹‖ ≤ (n + 1) Cⁿ ‖S − T‖`.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L174-L192
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L174-L192

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
omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem LieTrotter.norm_pow_succ_sub_pow_succ_le {S T : 𝔸} {C : ℝ} (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C)
    (n : ℕ) : ‖S ^ (n + 1) - T ^ (n + 1)‖ ≤ (n + 1) * C ^ n * ‖S - T‖ := by sorry
