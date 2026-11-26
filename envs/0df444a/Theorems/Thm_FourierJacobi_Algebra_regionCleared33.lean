-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_regionCleared33
-- name    : FourierJacobi.Algebra.regionCleared33
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:50:36.273826+00:00
-- url     : https://prove2.me/theorems/ba9fb5b3-3026-53ce-8f51-3f37f01609ba
-- title:
--   Algebra: region Cleared33
-- statement:
--   The Algebra construction uses the region Cleared33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/RegionSum.lean#L393-L400
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/RegionSum.lean#L393-L400

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_RegionSum
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem FourierJacobi.Algebra.regionCleared33 (t d U V P N E F G : K)
    (hd : d ≠ 0) (hP : P ≠ 0) (hN : N ≠ 0) (hE : E ≠ 0)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    (d ^ 2 * P * N * E * F * G) * regionTerm33 t d U V P N E F G =
      regionNumerator33 t d U V P N E F G := by sorry
