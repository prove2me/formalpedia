-- Prove2me | Theorems.Thm_Kyprianou_Ch05_passageTestStability
-- name    : Kyprianou.Ch05.passageTestStability
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T03:00:51.823931+00:00
-- url     : https://prove2.me/theorems/5abdb836-3991-4072-bada-0d8c6c35a9f6
-- title:
--   Theorem 5.7 (stability): passage expectation is 1-Lipschitz in the test
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, if two bounded continuous tests $f,g$ vanishing at $(0,0)$ differ uniformly by at most $\eta$, then at every level $x$ their passage test expectations differ by at most $\eta$: the passage expectation is an integral against a sub-probability law, hence $1$-Lipschitz in the test with respect to the uniform norm.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
/-- Passage-side stability: uniform closeness of tests bounds the passage expectation difference, at every level. -/
theorem passageTestStability
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0)) :
  ∀ f g : Real × Real → Real, IsBoundedContinuousTest f → IsBoundedContinuousTest g → f (0, 0) = 0 → g (0, 0) = 0 → ∀ η : Real, 0 < η → (∀ z : Real × Real, |f z - g z| ≤ η) → ∀ x : Real, |passageTestExpectation P Y Yleft death x f - passageTestExpectation P Y Yleft death x g| ≤ η := by
  sorry
end Kyprianou.Ch05
