-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_heightExpansion5
-- name    : FourierJacobi.Algebra.heightExpansion5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:45.85361+00:00
-- url     : https://prove2.me/theorems/f3a8ddaa-ea79-5aea-81fe-15fc07e7e20b
-- title:
--   Algebra: height Expansion5
-- statement:
--   The Algebra construction uses the height Expansion5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L361-L366
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L361-L366

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

theorem FourierJacobi.Algebra.heightExpansion5 (t a b d : K) :
    weylHeight5 t a b d = evalCoefficients d (whCoeffs5 t a b) := by sorry
