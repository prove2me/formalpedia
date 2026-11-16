-- Prove2me | Theorems.Thm_Kyprianou_Ch06_uniquenessOfAdmissibleWienerHopfFactors
-- name    : Kyprianou.Ch06.uniquenessOfAdmissibleWienerHopfFactors
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:11:11.648101+00:00
-- url     : https://prove2.me/theorems/8db8b31d-510b-4150-b6db-b4b808ca90c0
-- title:
--   Corollary 6.19: uniqueness of admissible Wiener–Hopf factors
-- statement:
--   For a real non-compound-Poisson Lévy process, any two Wiener-Hopf decompositions of the joint characteristic function p/(p-iϑ+Ψθ) into probability-law factors must coincide, provided each positive factor is infinitely divisible with spatial support in [0,∞), each negative factor has support in (-∞,0], and both spatial marginal supports accumulate at zero. These explicit admissibility restrictions reflect the Wiener-Hopf factors constructed in Theorem 6.16 and exclude arbitrary shift or trivial factorizations.
-- source:
--   Kyprianou (2006), Corollary 6.19, printed p. 167; physical PDF p. 89. Implicit uniqueness-hypothesis issue documented in source_issues_20261115.md.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleWienerHopfFactor
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Corollary 6.19: uniqueness of the two bivariate Wiener-Hopf factors
in the admissible half-line infinitely divisible class. Equality is
of full joint time-position laws, hence of their characteristic
functions, not merely of their product. -/
theorem uniquenessOfAdmissibleWienerHopfFactors
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real) (p : Real)
    (psi : Real → Complex)
    (muPlus muMinus nuPlus nuMinus : Measure (NNReal × Real))
    (hp : 0 < p)
    (hX : IsRealLevyProcess P X)
    (hNonCompound : ¬ IsCompoundPoissonProcess P X)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        Complex.exp (Complex.I *
          (↑(theta * X t omega) : Complex)) ∂P) =
        Complex.exp (-(↑(t : Real) : Complex) * psi theta))
    (hPositive : IsAdmissibleWienerHopfFactor true muPlus)
    (hNegative : IsAdmissibleWienerHopfFactor false muMinus)
    (hPositive' : IsAdmissibleWienerHopfFactor true nuPlus)
    (hNegative' : IsAdmissibleWienerHopfFactor false nuMinus)
    (hFirst : ∀ (vartheta theta : Real),
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂muPlus) *
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂muMinus) =
        (↑p : Complex) /
          ((↑p : Complex) -
            Complex.I * (↑vartheta : Complex) + psi theta))
    (hSecond : ∀ (vartheta theta : Real),
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂nuPlus) *
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂nuMinus) =
        (↑p : Complex) /
          ((↑p : Complex) -
            Complex.I * (↑vartheta : Complex) + psi theta)) :
    muPlus = nuPlus ∧ muMinus = nuMinus := by
  sorry

end Kyprianou.Ch06
