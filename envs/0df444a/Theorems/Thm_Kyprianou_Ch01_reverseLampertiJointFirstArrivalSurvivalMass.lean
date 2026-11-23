-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiJointFirstArrivalSurvivalMass
-- name    : Kyprianou.Ch01.reverseLampertiJointFirstArrivalSurvivalMass
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:42:19.033407+00:00
-- url     : https://prove2.me/theorems/8ecdd07d-6461-43f0-b1bd-f909d49e7cf4
-- title:
--   Equality of combined first-arrival survival mass and independent joint first-arrival mass
-- statement:
--   At initial populations a and b, the no-arrival probability for a+b equals the probability that two independent initial clocks each survive their scaled time. This ENNReal equality follows from the proved exponential survival identities.
-- source:
--   Kyprianou (2006), Section 1.3.4, first-arrival competing exponentials.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiJointFirstArrivalSurvivalMass
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (rate : NNReal) (hrate : 0 < rate)
    (arrival marks : Nat -> Omega -> Real)
    (jumpLaw : Measure Real) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (a b : Nat) (t : NNReal) :
    Q {omega : Omega | ((a + b : Nat) : Real) * (t : Real) <
      ProbabilityTheory.arrival arrival 0 omega} =
    (Q.prod Q) (Set.prod
      {omega : Omega | (a : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
      {omega : Omega | (b : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}) := by
  sorry
