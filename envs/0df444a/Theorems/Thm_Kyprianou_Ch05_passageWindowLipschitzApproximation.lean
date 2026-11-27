-- Prove2me | Theorems.Thm_Kyprianou_Ch05_passageWindowLipschitzApproximation
-- name    : Kyprianou.Ch05.passageWindowLipschitzApproximation
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:53:46.308651+00:00
-- url     : https://prove2.me/theorems/f1f9410d-37ce-4a9f-bfd5-40423a635158
-- title:
--   Theorem 5.7 (window convergence): Lipschitz approximation with both sides close
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, every bounded continuous test $f$ vanishing at $(0,0)$ and every $\varepsilon>0$ admit a Lipschitz bounded continuous test $g$, also vanishing at $(0,0)$, such that eventually both the passage test expectations of $f$ and $g$ and their window-truncated jump terms differ by at most $\varepsilon$. The passage side is stable because the passage law is a sub-probability; the jump side is stable because finite mean gives $\int_0^\infty \Pi((y,\infty))\,dy = \int z\,\Pi(dz) < \infty$, so a uniformly small perturbation of the test moves the truncated integral by a uniformly small amount.
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
/-- Every vanishing test admits a Lipschitz vanishing test whose passage
expectation and truncated jump term are eventually epsilon-close to its own. -/
theorem passageWindowLipschitzApproximation
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
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
    ∀ ε : Real, 0 < ε → ∃ g : Real × Real → Real,
      IsBoundedContinuousTest g ∧ g (0, 0) = 0 ∧
      (∃ C : Real, ∀ p q : Real × Real, |g p - g q| ≤ C * (|p.1 - q.1| + |p.2 - q.2|)) ∧
      ∀ᶠ x : Real in atTop,
        |passageTestExpectation P Y Yleft death x f - passageTestExpectation P Y Yleft death x g| ≤ ε ∧
        |(1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, g (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  sorry
end Kyprianou.Ch05
