-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_regionCleared16
-- name    : FourierJacobi.Algebra.regionCleared16
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:47:49.375613+00:00
-- url     : https://prove2.me/theorems/084e196c-ef42-460f-8d3f-1c9c8121ec7a
-- title:
--   Algebra: region Cleared16
-- statement:
--   The Algebra construction uses the region Cleared16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/RegionSum.lean#L206-L213
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/RegionSum.lean#L206-L213

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

theorem FourierJacobi.Algebra.regionCleared16 (t d U V P N E F G : K)
    (hd : d ≠ 0) (hP : P ≠ 0) (hN : N ≠ 0) (hE : E ≠ 0)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    (d ^ 2 * P * N * E * F * G) * regionTerm16 t d U V P N E F G =
      regionNumerator16 t d U V P N E F G := by sorry
