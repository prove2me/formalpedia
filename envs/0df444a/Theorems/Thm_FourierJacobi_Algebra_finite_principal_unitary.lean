-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finite_principal_unitary
-- name    : FourierJacobi.Algebra.finite_principal_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:20.348368+00:00
-- url     : https://prove2.me/theorems/bdb2276c-7534-57e7-8d30-b5497be70dc2
-- title:
--   Algebra: finite principal unitary
-- statement:
--   The finite principal formula, with no auxiliary denominator assumptions.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L105-L127
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L105-L127

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.finite_principal_unitary (q t : ℝ) (a b d : ℂ)
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (t : ℂ) a b d) *
      principalNormalizer (t : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * (t : ℂ)) * (1 + (t : ℂ) / d)) := by sorry
