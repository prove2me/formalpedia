-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finite_principal_square_roots
-- name    : FourierJacobi.Algebra.finite_principal_square_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:04.674898+00:00
-- url     : https://prove2.me/theorems/7026158f-4e24-50e0-8ac6-78313a2a7769
-- title:
--   Algebra: finite principal square roots
-- statement:
--   The paper's square-root notation, for the finite input on the regular locus.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L142-L153
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L142-L153

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.finite_principal_square_roots (q : ℝ) (hq : 1 < q) (a b d A B : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hA : A ^ 2 = a) (hB : B ^ 2 = b)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b d) *
      principalNormalizer (inverseSqrt q : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (A⁻¹ + A) ^ 2 * (B⁻¹ + B) ^ 2 /
        ((1 + d * (inverseSqrt q : ℂ)) * (1 + (inverseSqrt q : ℂ) / d)) := by sorry
