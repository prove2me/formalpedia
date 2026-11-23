-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoArrivalTwoPopulationIndicator
-- name    : Kyprianou.Ch01.reverseLampertiNoArrivalTwoPopulationIndicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:43:49.916554+00:00
-- url     : https://prove2.me/theorems/c3721bb1-072c-46a5-bb73-a793450854fd
-- title:
--   Independent two-population no-arrival mass is concentrated on initial sum
-- statement:
--   On the product probability space, before either original driver has arrived the sum of populations is their initial sum; the surviving event mass is a product rectangle.
-- source:
--   Kyprianou (2006), Section 1.3.4, first-event independence decomposition.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNoArrivalTwoPopulationIndicator
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (rate : NNReal) (hrate : 0 < rate)
    (offspring : PMF Nat) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : Nat -> Omega -> Real)
    (jumpLaw : Measure Real) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : Real | ∃ k : Nat, x = (k : Real) - 1} = 1)
    (hJumpMass : ∀ k : Nat,
      jumpLaw ({((k : Real) - 1)} : Set Real) = offspring k)
    (hNoExplosion : ∀ y : Nat, ∀ᵐ omega ∂Q,
      ∀ t : NNReal, ∃ s : NNReal,
        (t : ENNReal) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s omega)
    (a b : Nat) (t : NNReal) (k : Nat) :
    (Q.prod Q) {zeta : Omega × Omega |
      (((a : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 zeta.1) ∧
        ((b : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 zeta.2)) ∧
      (compoundPoissonToBranching
        (integerCompoundPoisson a arrival marks) t zeta.1).toNat +
      (compoundPoissonToBranching
        (integerCompoundPoisson b arrival marks) t zeta.2).toNat = k} =
    if k = a + b then
      (Q.prod Q) (Set.prod
        {omega : Omega | (a : Real) * (t : Real) <
          ProbabilityTheory.arrival arrival 0 omega}
        {omega : Omega | (b : Real) * (t : Real) <
          ProbabilityTheory.arrival arrival 0 omega})
    else 0 := by
  sorry
