-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_region_numerators_sum
-- name    : FourierJacobi.Algebra.region_numerators_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:10.62396+00:00
-- url     : https://prove2.me/theorems/53ee5d8b-17be-4d96-8289-491735b5aec2
-- title:
--   Algebra: region numerators sum
-- statement:
--   The Algebra construction uses the region numerators sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/RegionSum.lean#L666-L675
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/RegionSum.lean#L666-L675

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
set_option maxHeartbeats 8000000

theorem FourierJacobi.Algebra.region_numerators_sum (t d U V : K) (hd : d ≠ 0) :
    (∑ i : Fin 50, rawRegionNumerators t d U V
      (1 - d * V * t) (1 - V * t / d)
      (1 - V ^ 2 * t ^ 2) (1 - U * t ^ 2) (1 - U * t ^ 4) i) =
    (1 - V ^ 2 * t ^ 2) * (1 - U * t ^ 2) * (1 - U * t ^ 4) *
      kernelNumerator t d U V := by sorry
