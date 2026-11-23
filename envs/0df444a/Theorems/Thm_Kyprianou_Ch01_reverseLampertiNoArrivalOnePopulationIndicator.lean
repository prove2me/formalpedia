-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoArrivalOnePopulationIndicator
-- name    : Kyprianou.Ch01.reverseLampertiNoArrivalOnePopulationIndicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:43:46.45274+00:00
-- url     : https://prove2.me/theorems/39962367-5b2a-4fc9-b36e-aaa16d805596
-- title:
--   Single-population no-arrival mass is concentrated on the initial state
-- statement:
--   The one-driver process remains at its initial population before its first original arrival, hence its surviving mass occupies precisely that population state.
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

theorem Kyprianou.Ch01.reverseLampertiNoArrivalOnePopulationIndicator
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
    (y : Nat) (t : NNReal) (k : Nat) :
    Q {omega : Omega |
      ((y : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 omega) ∧
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) t omega).toNat = k} =
    if k = y then
      Q {omega : Omega | (y : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 omega}
    else 0 := by
  sorry
