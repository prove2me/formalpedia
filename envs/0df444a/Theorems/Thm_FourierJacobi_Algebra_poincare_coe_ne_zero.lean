-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_poincare_coe_ne_zero
-- name    : FourierJacobi.Algebra.poincare_coe_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:53.491676+00:00
-- url     : https://prove2.me/theorems/b3b4717e-8c51-591c-89a9-a12306e88edd
-- title:
--   Algebra: poincare coe ne zero
-- statement:
--   The Algebra construction uses the poincare coe ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L33-L38
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L33-L38

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.poincare_coe_ne_zero (t : ℝ) : poincare (t : ℂ) ≠ 0 := by sorry
