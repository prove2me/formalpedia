-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_remainingExpansion1
-- name    : FourierJacobi.Algebra.remainingExpansion1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:43.406809+00:00
-- url     : https://prove2.me/theorems/92264968-20e7-473c-9f84-aa90782c44fe
-- title:
--   Algebra: remaining Expansion1
-- statement:
--   The Algebra construction uses the remaining Expansion1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L175-L180
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L175-L180

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

theorem FourierJacobi.Algebra.remainingExpansion1 (t a b d : K) :
    weylRemainingFactors t a b d 1 = evalCoefficients d (wrCoeffs1 t a b) := by sorry
