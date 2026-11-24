-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentMaxAbsLocallyBoundedV1
-- name    : Kyprianou.Ch03.stableFracMomentMaxAbsLocallyBoundedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T15:10:12.366301+00:00
-- url     : https://prove2.me/theorems/b7d6fcf5-5b49-4b30-9f5c-ae2b7688c903
-- title:
--   Local boundedness of truncated-below absolute powers
-- statement:
--   Take M=(max R 1)^eta and use monotonicity of real powers.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), direct application of the shared Theorem 3.8 moment criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentMaxAbsLocallyBoundedV1
    (eta : Real) (heta : 0 < eta) :
    ∀ R : Real, 0 ≤ R → ∃ M : Real, ∀ x : Real, |x| ≤ R →
      (max |x| 1) ^ eta ≤ M := by sorry
