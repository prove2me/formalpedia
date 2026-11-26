-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_one_sub_mul_ne_zero_of_norm_lt_one
-- name    : FourierJacobi.Algebra.one_sub_mul_ne_zero_of_norm_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:43:27.281418+00:00
-- url     : https://prove2.me/theorems/00a86c79-f080-46c9-bf80-1e5cc78d6395
-- title:
--   Algebra: one sub mul ne zero of norm lt one
-- statement:
--   The Algebra construction uses the one sub mul ne zero of norm lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryParameters.lean#L21-L26
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryParameters.lean#L21-L26

import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.one_sub_mul_ne_zero_of_norm_lt_one {z x : ℂ}
    (hz : ‖z‖ = 1) (hx : ‖x‖ < 1) : 1 - z * x ≠ 0 := by sorry
