-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_heightExpansion4
-- name    : FourierJacobi.Algebra.heightExpansion4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:32.72781+00:00
-- url     : https://prove2.me/theorems/def5728f-0124-4fcc-9d63-4737b5cc7555
-- title:
--   Algebra: height Expansion4
-- statement:
--   The Algebra construction uses the height Expansion4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L313-L318
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L313-L318

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

theorem FourierJacobi.Algebra.heightExpansion4 (t a b d : K) :
    weylHeight4 t a b d = evalCoefficients d (whCoeffs4 t a b) := by sorry
