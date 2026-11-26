-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_remainingExpansion4
-- name    : FourierJacobi.Algebra.remainingExpansion4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:21.949368+00:00
-- url     : https://prove2.me/theorems/4c6fc632-fb0c-4ecc-9e98-a709da28d8cf
-- title:
--   Algebra: remaining Expansion4
-- statement:
--   The Algebra construction uses the remaining Expansion4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L319-L324
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L319-L324

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

theorem FourierJacobi.Algebra.remainingExpansion4 (t a b d : K) :
    weylRemainingFactors t a b d 4 = evalCoefficients d (wrCoeffs4 t a b) := by sorry
