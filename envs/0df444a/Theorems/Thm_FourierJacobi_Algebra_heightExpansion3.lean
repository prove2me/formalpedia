-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_heightExpansion3
-- name    : FourierJacobi.Algebra.heightExpansion3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:25.547554+00:00
-- url     : https://prove2.me/theorems/265caeb1-ba38-4a28-b012-12f7aa4065a0
-- title:
--   Algebra: height Expansion3
-- statement:
--   The Algebra construction uses the height Expansion3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L265-L270
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L265-L270

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

theorem FourierJacobi.Algebra.heightExpansion3 (t a b d : K) :
    weylHeight3 t a b d = evalCoefficients d (whCoeffs3 t a b) := by sorry
