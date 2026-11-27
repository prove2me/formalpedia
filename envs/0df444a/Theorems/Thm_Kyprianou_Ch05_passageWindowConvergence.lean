-- Prove2me | Theorems.Thm_Kyprianou_Ch05_passageWindowConvergence
-- name    : Kyprianou.Ch05.passageWindowConvergence
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:37:09.301352+00:00
-- url     : https://prove2.me/theorems/44aa8866-a45d-4b17-9d90-27e324849b49
-- title:
--   Theorem 5.7 (vanishing tests): passage expectation tracks the window-truncated jump term
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, for every bounded continuous test $f$ vanishing at $(0,0)$ and every $\varepsilon>0$, the passage test expectation at level $x$ differs from the window-truncated jump term (outer renewal integral over starting heights $y\in[0,x]$) by at most $\varepsilon$ eventually. This is the two-sided form of the renewal convergence on the growing window: the key-renewal heart of the vanishing-test step, isolated from the tail of the jump integral.
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
/-- Two-sided window convergence: passage test expectation minus the truncated jump term is eventually within epsilon. -/
theorem passageWindowConvergence
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
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, |passageTestExpectation P Y Yleft death x f - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  sorry
end Kyprianou.Ch05
