-- Prove2me | Theorems.Thm_Kyprianou_Ch06_positiveHalfLineRegularityClassification
-- name    : Kyprianou.Ch06.positiveHalfLineRegularityClassification
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:08:23.571451+00:00
-- url     : https://prove2.me/theorems/e2f161d7-2504-4326-8b03-eadd265ca34c
-- title:
--   Theorem 6.5: full positive-half-line regularity classification
-- statement:
--   For every Lévy process other than compound Poisson, prove that zero is regular for (0,∞) precisely when ∫₀¹P(X_t>0)dt/t diverges. Prove that divergence holds precisely in any of the three source cases: (i) unbounded variation; (ii) bounded variation and positive linear drift d; (iii) bounded variation and zero drift with the specified Lévy-measure ratio integral ∫₀¹xΠ(dx)/∫₀ˣΠ(-∞,-y)dy diverging. The triplet conditions distinguish bounded variation and identify the finite-variation drift.
-- source:
--   Kyprianou (2006), Theorem 6.5, printed pp. 142–143; two-up PDF pp. 76–77.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Theorem 6.5: for any non-compound-Poisson real Lévy process,
regularity for the open positive half-line is equivalent to divergence
of the Spitzer integral and, in turn, to exactly one of the three
bounded/unbounded variation conditions in the source. In the zero-drift
case the denominator is the integrated negative Lévy tail. -/
theorem positiveHalfLineRegularityClassification
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b d : Real) (sigma2 : NNReal) (nu : Measure Real)
    (hX : IsRealLevyProcess P X)
    (hTriplet : IsLevyKhintchineTriplet P X b sigma2 nu)
    (hDrift : (sigma2 = 0 ∧
      (∫⁻ x in {x : Real | |x| < 1},
        ENNReal.ofReal |x| ∂nu) < ⊤) →
      d = b - ∫ x in {x : Real | |x| < 1}, x ∂nu)
    (hNonCompound : ¬ IsCompoundPoissonProcess P X) :
    (IsRegularFor P X 0 (Set.Ioi 0) ↔
      PositiveOccupationDiverges P X) ∧
    (PositiveOccupationDiverges P X ↔
      (¬ (sigma2 = 0 ∧
        (∫⁻ x in {x : Real | |x| < 1},
          ENNReal.ofReal |x| ∂nu) < ⊤)) ∨
      ((sigma2 = 0 ∧
        (∫⁻ x in {x : Real | |x| < 1},
          ENNReal.ofReal |x| ∂nu) < ⊤) ∧ 0 < d) ∨
      ((sigma2 = 0 ∧
        (∫⁻ x in {x : Real | |x| < 1},
          ENNReal.ofReal |x| ∂nu) < ⊤) ∧
        d = 0 ∧
        (∫⁻ x in Set.Ioo (0 : Real) 1,
          (ENNReal.ofReal x) /
            (∫⁻ y in Set.Ioo (0 : Real) x,
              nu (Set.Iio (-y)) ∂volume) ∂nu) = ⊤)) := by
  sorry

end Kyprianou.Ch06
