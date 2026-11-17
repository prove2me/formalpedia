-- Prove2me | Theorems.Thm_Kyprianou_Ch07_gaussianComponentUpwardCreeping
-- name    : Kyprianou.Ch07.gaussianComponentUpwardCreeping
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:33:03.106047+00:00
-- url     : https://prove2.me/theorems/690b283d-89b0-46df-9fbd-ae91a3887e75
-- title:
--   Theorem 7.11(ii): a nonzero Gaussian component forces upward creeping
-- statement:
--   Use Gaussian component to prove nonzero ascending ladder-height drift and upward creeping.
-- source:
--   Kyprianou (2006), Chapter 7, Theorem 7.11, printed pp. 198–199, original PDF pp. 207–208. Source exact component of the complete published criterion 47cb7a5c-0315-4679-8c52-f417ee7ff7f6. The challenging Vigon (2002) pure-jump case is retained as a separate full-strength obligation.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.gaussianComponentUpwardCreeping
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi) :
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    let unboundedPureJump : Prop :=
      sigma2 = 0 ∧ ¬ finiteVariationJumpMass
    let mixedJumpCriterion : Prop :=
      (∫⁻ x : Real in Set.Ioo 0 1,
         (ENNReal.ofReal x * Pi (Set.Ioi x)) /
         (∫⁻ u : Real in Set.Ioo 0 x,
            Pi (Set.Ioo (-1) (-u)) ∂volume) ∂volume) < ⊤
    0 < sigma2 →
      0 < Kyprianou.Ch05.creepingProbability P X (fun _ => (⊤ : WithTop NNReal)) 1 := by
  sorry
