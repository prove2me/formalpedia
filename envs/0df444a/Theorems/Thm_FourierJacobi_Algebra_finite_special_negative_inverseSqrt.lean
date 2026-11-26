-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finite_special_negative_inverseSqrt
-- name    : FourierJacobi.Algebra.finite_special_negative_inverseSqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:20:22.576381+00:00
-- url     : https://prove2.me/theorems/94308dfe-830c-5077-a525-efa9cba07e69
-- title:
--   Algebra: finite special negative inverse Sqrt
-- statement:
--   The Algebra construction uses the finite special negative inverse Sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L245-L252
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L245-L252

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.finite_special_negative_inverseSqrt (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b (-(inverseSqrt q : ℂ))) *
      specialNormalizer (inverseSqrt q : ℂ) a b (-1) = 2 / ((q : ℂ) + 1) := by sorry
