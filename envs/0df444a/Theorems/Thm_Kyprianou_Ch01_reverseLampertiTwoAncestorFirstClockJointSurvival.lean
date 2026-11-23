-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoAncestorFirstClockJointSurvival
-- name    : Kyprianou.Ch01.reverseLampertiTwoAncestorFirstClockJointSurvival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:01:06.614582+00:00
-- url     : https://prove2.me/theorems/f39480a3-4df9-4596-ae96-71b97fac9c27
-- title:
--   Joint survival of two independent initial reverse Lamperti arrival clocks
-- statement:
--   Two independent compound-Poisson driver copies have probability exp(-rate*(a+b)*t) that neither of their first arrival times has occurred by the respective thresholds a*t and b*t. This supplies the first competing exponential-clock survival law in the positive-time ancestor coupling argument.
-- source:
--   Kyprianou (2006), Section 1.3.4, competing initial exponential clocks.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiTwoAncestorFirstClockJointSurvival
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (rate : NNReal) (hrate : 0 < rate)
    (arrival marks : Nat -> Omega -> Real)
    (jumpLaw : Measure Real) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (a b : Nat) (t : NNReal) :
    ((Q.prod Q) (Set.prod
      {omega : Omega | (a : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
      {omega : Omega | (b : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega})).toReal =
    Real.exp (-((rate : Real) *
      (((a + b : Nat) : Real) * (t : Real)))) := by
  sorry
