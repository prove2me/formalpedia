-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_one_add_inv_ne_zero
-- name    : FourierJacobi.Algebra.one_add_inv_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:33.686482+00:00
-- url     : https://prove2.me/theorems/bcae5b65-0784-57fd-85fd-c598c63d77bc
-- title:
--   Algebra: one add inv ne zero
-- statement:
--   The Algebra construction uses the one add inv ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L155-L160
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L155-L160

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.one_add_inv_ne_zero {z : ℂ} (hz : z ≠ 0) (h : 1 + z ≠ 0) :
    1 + z⁻¹ ≠ 0 := by sorry
