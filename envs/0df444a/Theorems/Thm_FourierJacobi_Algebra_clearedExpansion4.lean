-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_clearedExpansion4
-- name    : FourierJacobi.Algebra.clearedExpansion4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:19.922791+00:00
-- url     : https://prove2.me/theorems/752c272f-3bc6-5ae0-a8b1-00a675984043
-- title:
--   Algebra: cleared Expansion4
-- statement:
--   The Algebra construction uses the cleared Expansion4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L325-L333
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L325-L333

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

theorem FourierJacobi.Algebra.clearedExpansion4 (t a b d : K) :
    weylClearedTerms t a b d 4 = evalCoefficients d (wcCoeffs4 t a b) := by sorry
