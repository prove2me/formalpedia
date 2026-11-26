-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_heightExpansion7
-- name    : FourierJacobi.Algebra.heightExpansion7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:09.696048+00:00
-- url     : https://prove2.me/theorems/67a0d597-a0fa-53f2-b8d8-51b14953a0db
-- title:
--   Algebra: height Expansion7
-- statement:
--   The Algebra construction uses the height Expansion7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L457-L462
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L457-L462

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem FourierJacobi.Algebra.heightExpansion7 (t a b d : K) :
    weylHeight7 t a b d = evalCoefficients d (whCoeffs7 t a b) := by sorry
