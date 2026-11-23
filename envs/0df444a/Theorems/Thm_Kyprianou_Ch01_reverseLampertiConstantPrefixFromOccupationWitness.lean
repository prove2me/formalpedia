-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixFromOccupationWitness
-- name    : Kyprianou.Ch01.reverseLampertiConstantPrefixFromOccupationWitness
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T14:03:39.205682+00:00
-- url     : https://prove2.me/theorems/20bc58ae-e171-4732-b4ed-c3a6480e53b6
-- title:
--   Deterministic constant-prefix reverse Lamperti clock bound from an occupation witness
-- statement:
--   If an integer-valued path is identically y before a physical time A and some physical time strictly below A has reciprocal occupation exceeding branching time t, then the reverse Lamperti time-changed state at t is y.
-- source:
--   Kyprianou (2006), Section 1.3.4, equation (1.19), right inverse of reciprocal occupation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiConstantPrefixFromOccupationWitness
    {Omega : Type*} (X : NNReal -> Omega -> Int) (omega : Omega)
    (y : Nat) (t : NNReal) (A : Real)
    (hConst : ∀ s : NNReal, (s : Real) < A -> X s omega = (y : Int))
    (hWitness : ∃ s : NNReal, (s : Real) < A ∧
      (t : ENNReal) < reciprocalOccupation X s omega) :
    (compoundPoissonToBranching X t omega).toNat = y := by
  sorry
