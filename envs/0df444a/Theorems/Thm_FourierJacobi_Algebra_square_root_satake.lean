-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_square_root_satake
-- name    : FourierJacobi.Algebra.square_root_satake
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:18:56.925662+00:00
-- url     : https://prove2.me/theorems/ab687d68-c1c1-53ae-b59d-79f5d8444d2a
-- title:
--   Algebra: square root satake
-- statement:
--   The squared expression in the paper is independent of the chosen square root.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L16-L26
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L16-L26

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.square_root_satake {K : Type*} [Field K] (a z : K)
    (ha : a ≠ 0) (hz : z ^ 2 = a) :
    (z⁻¹ + z) ^ 2 = a + 2 + a⁻¹ := by sorry
