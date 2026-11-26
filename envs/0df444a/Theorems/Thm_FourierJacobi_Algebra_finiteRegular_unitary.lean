-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finiteRegular_unitary
-- name    : FourierJacobi.Algebra.finiteRegular_unitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:19:18.212348+00:00
-- url     : https://prove2.me/theorems/8da223fa-4c83-5a50-9eb7-fccce505e324
-- title:
--   Algebra: finite Regular unitary
-- statement:
--   The Algebra construction uses the finite Regular unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L79-L102
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L79-L102

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.finiteRegular_unitary {t : ℝ} {a b d : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) : FiniteRegular (t : ℂ) a b d := by sorry
