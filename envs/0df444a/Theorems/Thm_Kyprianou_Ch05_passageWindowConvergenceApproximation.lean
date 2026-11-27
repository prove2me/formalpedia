-- Prove2me | Theorems.Thm_Kyprianou_Ch05_passageWindowConvergenceApproximation
-- name    : Kyprianou.Ch05.passageWindowConvergenceApproximation
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:44:53.114882+00:00
-- url     : https://prove2.me/theorems/f1075454-2d3f-4618-8cd2-e656d59032a1
-- title:
--   Theorem 5.7 (window convergence): Lipschitz case implies the general case
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, if the window convergence of the passage test expectation to the truncated jump term holds for every Lipschitz bounded continuous test vanishing at $(0,0)$, then it holds for every such test. Bounded continuous tests are approximated uniformly on the relevant domain by Lipschitz tests, and both the passage expectation and the truncated jump term are stable under uniform approximation of the test.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121, via Lemma 5.5, pp. 116-117.

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
/-- Approximation step: window convergence for all Lipschitz vanishing tests implies it for all vanishing tests. -/
theorem passageWindowConvergenceApproximation
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
  (∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 → (∃ C : Real, ∀ p q : Real × Real, |f p - f q| ≤ C * (|p.1 - q.1| + |p.2 - q.2|)) → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, |passageTestExpectation P Y Yleft death x f - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε) → ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, |passageTestExpectation P Y Yleft death x f - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  sorry
end Kyprianou.Ch05
