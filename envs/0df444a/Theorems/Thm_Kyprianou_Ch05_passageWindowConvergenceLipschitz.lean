-- Prove2me | Theorems.Thm_Kyprianou_Ch05_passageWindowConvergenceLipschitz
-- name    : Kyprianou.Ch05.passageWindowConvergenceLipschitz
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:44:47.786691+00:00
-- url     : https://prove2.me/theorems/c6b3bb35-21ed-52bc-98d0-b392e507c364
-- title:
--   Theorem 5.7 (window convergence, Lipschitz tests): passage expectation tracks the truncated jump term
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, the window convergence of the passage test expectation to the truncated jump term holds for bounded continuous tests that vanish at $(0,0)$ and are Lipschitz. For Lipschitz tests the key renewal theorem applies directly to the renewal convolution, so this is the core case of the window step.
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
/-- Window convergence for Lipschitz vanishing tests. -/
theorem passageWindowConvergenceLipschitz
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
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 → (∃ C : Real, ∀ p q : Real × Real, |f p - f q| ≤ C * (|p.1 - q.1| + |p.2 - q.2|)) → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, |passageTestExpectation P Y Yleft death x f - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  sorry
end Kyprianou.Ch05
