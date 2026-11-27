-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingProbabilityLowerBoundEventually
-- name    : Kyprianou.Ch05.creepingProbabilityLowerBoundEventually
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:16:05.894924+00:00
-- url     : https://prove2.me/theorems/51b07e6b-d1d6-49f2-b947-79282259e11f
-- title:
--   Theorem 5.7 (creeping bridge, lower): eventual lower sandwich bound
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 together with the potential interval limits $(U\,0)(x,x+y]\to y/\mu$, for every $\varepsilon>0$ the creeping probability at level $x$ is eventually at least $d/\mu-\varepsilon$. This is the lower half of the interval sandwich that proves the creeping bridge: the creeping mass is the drift part of the potential measure, so large-level creeping is controlled below by potential interval masses.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121 (creeping conjunct), via Corollary 5.3, p. 114.

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
/-- Lower sandwich half of the creeping bridge: the creeping probability is eventually at least d/mu - epsilon. -/
theorem creepingProbabilityLowerBoundEventually
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
    (hNonLattice : NonLatticeMeasure (U 0))
    (hPotLim : ∀ y : Real, 0 < y →
      Tendsto (fun x : Real => ((U 0) (Set.Ioc x (x + y))).toReal)
        atTop (nhds (y / (∫ omega, Y 1 omega ∂P)))) :
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop,
    d / (∫ omega, Y 1 omega ∂P) - ε ≤ creepingProbability P Y death x := by
  sorry
end Kyprianou.Ch05
