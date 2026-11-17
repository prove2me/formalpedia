-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_6_IrregularAtZeroPrecludesCreeping
-- name    : Kyprianou.Ch07.exercise7_6_IrregularAtZeroPrecludesCreeping
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T22:07:54.883414+00:00
-- url     : https://prove2.me/theorems/3bdb27c7-b29d-4576-b4e5-128f39de93f1
-- title:
--   Kyprianou Exercise 7.6(3): irregularity at zero precludes upward creeping
-- statement:
--   This is the exact independently quantified source subpart 3 of Kyprianou Chapter 7 Exercise 7.6, maintaining the full original Lévy process, characteristic exponent and Lévy triplet hypotheses, with its own case-specific assumptions in the conclusion.
-- source:
--   Kyprianou (2006), Chapter 7, Exercise 7.6(i)–(v), printed pp. 208–209; original PDF pp. 217–218, source solutions at original PDF pp. 345–347. Exact top-level conjunction subpart from published theorem dce92d6f-c48f-4d45-b69f-5454cf4804ad, extracted without rewriting the underlying proposition.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.exercise7_6_IrregularAtZeroPrecludesCreeping
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta)) :
    let upCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) 1
    let downCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P (fun t omega => -X t omega)
          (fun _ => (⊤ : WithTop NNReal)) 1
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    (Kyprianou.Ch06.IsIrregularFor P X 0 (Set.Ioi 0) →
       ¬ upCreeps) := by
  sorry
