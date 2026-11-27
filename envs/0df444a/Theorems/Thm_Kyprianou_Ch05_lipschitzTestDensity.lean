-- Prove2me | Theorems.Thm_Kyprianou_Ch05_lipschitzTestDensity
-- name    : Kyprianou.Ch05.lipschitzTestDensity
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:57:29.865831+00:00
-- url     : https://prove2.me/theorems/6fbad076-bcc4-5633-b07a-1a5ae9aa22d3
-- title:
--   Theorem 5.7 (approximation): Lipschitz vanishing tests are uniformly dense
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, every bounded continuous test $f$ vanishing at $(0,0)$ can be approximated uniformly to within any $\eta>0$ by a Lipschitz bounded continuous test $g$ that also vanishes at $(0,0)$. This is the pure approximation-theory ingredient of the window step: mollification and truncation of the test function.
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
/-- Uniform density of Lipschitz vanishing tests among vanishing bounded continuous tests. -/
theorem lipschitzTestDensity
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
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 → ∀ η : Real, 0 < η → ∃ g : Real × Real → Real, IsBoundedContinuousTest g ∧ g (0, 0) = 0 ∧ (∃ C : Real, ∀ p q : Real × Real, |g p - g q| ≤ C * (|p.1 - q.1| + |p.2 - q.2|)) ∧ ∀ z : Real × Real, |f z - g z| ≤ η := by
  sorry
end Kyprianou.Ch05
