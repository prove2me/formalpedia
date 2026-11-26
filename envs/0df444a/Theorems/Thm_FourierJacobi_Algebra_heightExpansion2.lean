-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_heightExpansion2
-- name    : FourierJacobi.Algebra.heightExpansion2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:50.71788+00:00
-- url     : https://prove2.me/theorems/c82f9050-7bdb-474b-a22a-0e882c6ab5ce
-- title:
--   Algebra: height Expansion2
-- statement:
--   The Algebra construction uses the height Expansion2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L217-L222
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean#L217-L222

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

theorem FourierJacobi.Algebra.heightExpansion2 (t a b d : K) :
    weylHeight2 t a b d = evalCoefficients d (whCoeffs2 t a b) := by sorry
