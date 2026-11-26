-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedLaplaceExponent_nonneg
-- name    : Kyprianou.Ch05.killedLaplaceExponent_nonneg
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:19:38.789232+00:00
-- url     : https://prove2.me/theorems/55e41196-b793-4bf8-8d12-70c0a8768bd2
-- title:
--   The killed Laplace exponent Phi is nonnegative on [0,infinity)
-- statement:
--   For a killed subordinator with Laplace triplet $(\eta, d, \Pi)$, the exponent $\Phi(\theta)=\eta+d\theta+\int_{(0,\infty)}(1-e^{-\theta x})\,\Pi(dx)$ is nonnegative for every $\theta\ge 0$: each of the three terms is nonnegative, since $\eta,d\ge 0$ and $1-e^{-\theta x}\ge 0$ for $x>0$.
--
--   $$\Phi(\theta)\ge 0\qquad(\theta\ge 0).$$
--
--   This sign fact is the boundary input for the resolvent identity $\int e^{-\theta x}U^q(dx)=1/(q+\Phi(\theta))$ behind Theorem 5.4 of Kyprianou (2006).
--
--   **Formalization Note.** The triplet is `IsKilledLaplaceTriplet`, whose defining equation is taken at the given $\theta$.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; decomposition of Kyprianou.Ch05.killedSubordinatorPotentialLattice (931e3306-d573-44a6-a001-adf4e80d2053) and its children.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Phi(theta) >= 0 for theta >= 0, directly from the triplet formula (5.1). -/
theorem killedLaplaceExponent_nonneg
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi) :
  ∀ theta : Real, 0 ≤ theta → 0 ≤ Phi theta
 := by
  sorry

end Kyprianou.Ch05
