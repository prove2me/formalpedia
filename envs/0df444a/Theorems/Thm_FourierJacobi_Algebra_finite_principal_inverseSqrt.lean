-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finite_principal_inverseSqrt
-- name    : FourierJacobi.Algebra.finite_principal_inverseSqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:23.011941+00:00
-- url     : https://prove2.me/theorems/b1b5612e-0827-4587-9df2-1d028fffacf4
-- title:
--   Algebra: finite principal inverse Sqrt
-- statement:
--   Substitute the positive square-root branch required by the paper.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L130-L139
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L130-L139

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.finite_principal_inverseSqrt (q : ℝ) (hq : 1 < q) (a b d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b d) *
      principalNormalizer (inverseSqrt q : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * (inverseSqrt q : ℂ)) * (1 + (inverseSqrt q : ℂ) / d)) := by sorry
