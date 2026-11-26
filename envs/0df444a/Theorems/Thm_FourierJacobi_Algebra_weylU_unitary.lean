-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weylU_unitary
-- name    : FourierJacobi.Algebra.weylU_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:35.088148+00:00
-- url     : https://prove2.me/theorems/88c2900b-8375-5c53-9205-2af21ac44709
-- title:
--   Algebra: weyl U unitary
-- statement:
--   The Algebra construction uses the weyl U unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L54-L56
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L54-L56

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.weylU_unitary {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (i : Fin 8) :
    ‖weylU a b i‖ = 1 := by sorry
