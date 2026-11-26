-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_regionRegular_special_negative
-- name    : FourierJacobi.Algebra.regionRegular_special_negative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:24:40.679738+00:00
-- url     : https://prove2.me/theorems/7b4c28ed-42a0-4dc6-9f1c-de798d7f92e6
-- title:
--   Algebra: region Regular special negative
-- statement:
--   The Algebra construction uses the region Regular special negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L182-L194
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L182-L194

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.regionRegular_special_negative {t : ℝ} {U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hU : ‖U‖ = 1) (hV : ‖V‖ = 1)
    (hV₁ : 1 + V ≠ 0) : RegionRegular (t : ℂ) (-(t : ℂ)) U V := by sorry
