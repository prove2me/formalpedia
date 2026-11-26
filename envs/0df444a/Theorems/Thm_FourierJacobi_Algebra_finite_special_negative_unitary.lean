-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finite_special_negative_unitary
-- name    : FourierJacobi.Algebra.finite_special_negative_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:07.542795+00:00
-- url     : https://prove2.me/theorems/5e9284a2-8ecc-4c6f-984d-78f5d71f6266
-- title:
--   Algebra: finite special negative unitary
-- statement:
--   The finite negative-special formula on the regular unitary Satake locus.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L228-L243
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L228-L243

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.finite_special_negative_unitary (q t : ℝ) (a b : ℂ)
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (t : ℂ) a b (-(t : ℂ))) *
      specialNormalizer (t : ℂ) a b (-1) = 2 / ((q : ℂ) + 1) := by sorry
