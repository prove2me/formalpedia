-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finiteRegular_special_negative
-- name    : FourierJacobi.Algebra.finiteRegular_special_negative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:19:52.018843+00:00
-- url     : https://prove2.me/theorems/747be4e3-7895-4325-97bc-e63c97acc6c7
-- title:
--   Algebra: finite Regular special negative
-- statement:
--   The Algebra construction uses the finite Regular special negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L196-L225
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L196-L225

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.finiteRegular_special_negative {t : ℝ} {a b : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    FiniteRegular (t : ℂ) a b (-(t : ℂ)) := by sorry
