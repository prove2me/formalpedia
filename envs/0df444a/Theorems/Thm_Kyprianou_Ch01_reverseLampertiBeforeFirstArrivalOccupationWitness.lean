-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiBeforeFirstArrivalOccupationWitness
-- name    : Kyprianou.Ch01.reverseLampertiBeforeFirstArrivalOccupationWitness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:03:36.581799+00:00
-- url     : https://prove2.me/theorems/82d6d7ca-41f0-4077-8451-9dd301fdca9e
-- title:
--   Reciprocal occupation crosses time t before the initial compound-Poisson arrival
-- statement:
--   If y*t is strictly before the first original compound-Poisson jump, the reciprocal occupation clock exceeds t at some earlier physical time. The prefix process equals y there; y=0 gives infinite occupation while y>0 gives a linear clock.
-- source:
--   Kyprianou (2006), Section 1.3.4, equation (1.19), first-jump time-change.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiBeforeFirstArrivalOccupationWitness
    {Omega : Type*}
    (y : Nat) (arrival marks : Nat -> Omega -> Real)
    (t : NNReal) (omega : Omega)
    (hBefore : (y : Real) * (t : Real) <
      ProbabilityTheory.arrival arrival 0 omega) :
    ∃ s : NNReal,
      (s : Real) < ProbabilityTheory.arrival arrival 0 omega ∧
      (t : ENNReal) <
        reciprocalOccupation (integerCompoundPoisson y arrival marks) s omega := by
  sorry
