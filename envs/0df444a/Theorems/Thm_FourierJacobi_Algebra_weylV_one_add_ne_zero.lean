-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weylV_one_add_ne_zero
-- name    : FourierJacobi.Algebra.weylV_one_add_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:57.291485+00:00
-- url     : https://prove2.me/theorems/a3465bc7-e077-45e7-88c9-0b6f1a2e7fce
-- title:
--   Algebra: weyl V one add ne zero
-- statement:
--   The Algebra construction uses the weyl V one add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L162-L175
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L162-L175

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.weylV_one_add_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) (i : Fin 8) :
    1 + weylV a b i ≠ 0 := by sorry
