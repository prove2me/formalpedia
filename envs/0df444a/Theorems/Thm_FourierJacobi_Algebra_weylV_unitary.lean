-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weylV_unitary
-- name    : FourierJacobi.Algebra.weylV_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:07.979962+00:00
-- url     : https://prove2.me/theorems/9beaa736-8ea1-4009-93e0-70756c338abf
-- title:
--   Algebra: weyl V unitary
-- statement:
--   The Algebra construction uses the weyl V unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L58-L60
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L58-L60

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.weylV_unitary {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (i : Fin 8) :
    ‖weylV a b i‖ = 1 := by sorry
