-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_clearedExpansion2
-- name    : FourierJacobi.Algebra.clearedExpansion2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:05.611824+00:00
-- url     : https://prove2.me/theorems/6bfedc47-b918-5ea7-8326-0b79a023aa0b
-- title:
--   Algebra: cleared Expansion2
-- statement:
--   The Algebra construction uses the cleared Expansion2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L229-L237
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L229-L237

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

theorem FourierJacobi.Algebra.clearedExpansion2 (t a b d : K) :
    weylClearedTerms t a b d 2 = evalCoefficients d (wcCoeffs2 t a b) := by sorry
