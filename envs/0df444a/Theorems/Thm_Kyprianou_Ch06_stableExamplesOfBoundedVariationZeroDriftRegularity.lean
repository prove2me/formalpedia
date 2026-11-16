-- Prove2me | Theorems.Thm_Kyprianou_Ch06_stableExamplesOfBoundedVariationZeroDriftRegularity
-- name    : Kyprianou.Ch06.stableExamplesOfBoundedVariationZeroDriftRegularity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:07:39.584959+00:00
-- url     : https://prove2.me/theorems/bc5e9db8-d48a-4574-b406-e8d2f01c369d
-- title:
--   Exercise 6.1: bounded-variation zero-drift examples of regularity
-- statement:
--   Construct two explicit bounded-variation Lévy laws with zero deterministic drift. A symmetric strictly α-stable process, 0<α<1, has origin regular for both positive and negative open half-lines. A positive α-stable subordinator is regular for the positive half-line but irregular for the negative half-line. Identify the laws by their characteristic/Laplace transforms and require sample paths to have locally bounded variation.
-- source:
--   Kyprianou (2006), Exercise 6.1, printed pp. 174–175; physical PDF pp. 92–93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.1: both requested examples can be chosen from strictly
alpha-stable real Levy processes, for the same index 0 < alpha < 1.
The symmetric example has both signs regular; the positive stable
subordinator has only the positive half-line regular. Their respective
characteristic and Laplace transforms identify the processes uniquely
in law, including the absence of deterministic drift. -/
theorem stableExamplesOfBoundedVariationZeroDriftRegularity :
    ∃ (alpha : Real) (Pboth Ppositive : Measure (NNReal → Real)),
      0 < alpha ∧ alpha < 1 ∧
      IsProbabilityMeasure Pboth ∧
      IsProbabilityMeasure Ppositive ∧
      IsRealLevyProcess Pboth (fun t omega => omega t) ∧
      IsRealLevyProcess Ppositive (fun t omega => omega t) ∧
      (∀ (t : NNReal) (theta : Real),
        (∫ omega : NNReal → Real,
          Complex.exp (Complex.I *
            (↑(theta * omega t) : Complex)) ∂Pboth) =
          Complex.exp (↑(-(t : Real) * (|theta| ^ alpha)) : Complex)) ∧
      (∀ (t : NNReal) (lambda : Real), 0 ≤ lambda →
        (∫ omega : NNReal → Real,
          Real.exp (-(lambda * omega t)) ∂Ppositive) =
          Real.exp (-(t : Real) * (lambda ^ alpha))) ∧
      IsRegularFor Pboth (fun t omega => omega t) 0 (Set.Ioi 0) ∧
      IsRegularFor Pboth (fun t omega => omega t) 0 (Set.Iio 0) ∧
      IsRegularFor Ppositive (fun t omega => omega t) 0 (Set.Ioi 0) ∧
      IsIrregularFor Ppositive (fun t omega => omega t) 0 (Set.Iio 0) ∧
      (∀ᵐ omega ∂Ppositive, ∀ t : NNReal, 0 ≤ omega t) ∧
      (∀ Q ∈ ({Pboth, Ppositive} : Set (Measure (NNReal → Real))),
        ∀ᵐ omega ∂Q, ∀ T : NNReal,
          ∃ C : Real, 0 ≤ C ∧
            ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
              StrictMono times → times (Fin.last n) ≤ T →
              (∑ i : Fin n,
                |omega (times i.succ) -
                  omega (times i.castSucc)|) ≤ C) := by
  sorry

end Kyprianou.Ch06
