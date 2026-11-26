-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_clearedExpansion6
-- name    : FourierJacobi.Algebra.clearedExpansion6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:30.896683+00:00
-- url     : https://prove2.me/theorems/f5cd4297-de1b-569a-b6fe-1c2571ec3632
-- title:
--   Algebra: cleared Expansion6
-- statement:
--   The Algebra construction uses the cleared Expansion6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L421-L429
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L421-L429

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

theorem FourierJacobi.Algebra.clearedExpansion6 (t a b d : K) :
    weylClearedTerms t a b d 6 = evalCoefficients d (wcCoeffs6 t a b) := by sorry
