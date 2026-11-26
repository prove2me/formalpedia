-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_heightExpansion0
-- name    : FourierJacobi.Algebra.heightExpansion0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:41.660823+00:00
-- url     : https://prove2.me/theorems/07ccfad7-1a6d-5001-8261-d84119f2cea0
-- title:
--   Algebra: height Expansion0
-- statement:
--   The Algebra construction uses the height Expansion0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L121-L126
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L121-L126

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

theorem FourierJacobi.Algebra.heightExpansion0 (t a b d : K) :
    weylHeight0 t a b d = evalCoefficients d (whCoeffs0 t a b) := by sorry
