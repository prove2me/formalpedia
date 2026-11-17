-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_6_StableNoCreepingPointHitting
-- name    : Kyprianou.Ch07.exercise7_6_StableNoCreepingPointHitting
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T22:08:15.098072+00:00
-- url     : https://prove2.me/theorems/e269fb01-2222-48a3-b0d1-0db169f1ea3b
-- title:
--   Kyprianou Exercise 7.6(5): stable-process no creeping and strictly positive point hitting
-- statement:
--   This is the exact independently quantified source subpart 5 of Kyprianou Chapter 7 Exercise 7.6, maintaining the full original Lévy process, characteristic exponent and Lévy triplet hypotheses, with its own case-specific assumptions in the conclusion.
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

theorem Kyprianou.Ch07.exercise7_6_StableNoCreepingPointHitting
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
    (∀ alpha : Real, 1 < alpha → alpha < 2 →
       (∃ c : Real, 0 < c ∧ ∀ theta : Real,
         Psi theta = ((c * |theta| ^ alpha : Real) : Complex)) →
       (¬ upCreeps ∧ ¬ downCreeps ∧
         ∀ x : Real, 0 < P {omega : Omega |
           ∃ t : NNReal, 0 < t ∧ X t omega = x})) := by
  sorry
