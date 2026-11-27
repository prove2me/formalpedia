-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingProbabilityUpperBoundEventually
-- name    : Kyprianou.Ch05.creepingProbabilityUpperBoundEventually
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:15:57.613315+00:00
-- url     : https://prove2.me/theorems/1bde78b2-4186-5fa6-8a4a-3872466301a1
-- title:
--   Theorem 5.7 (creeping bridge, upper): eventual upper sandwich bound
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 together with the potential interval limits $(U\,0)(x,x+y]\to y/\mu$, for every $\varepsilon>0$ the creeping probability at level $x$ is eventually at most $d/\mu+\varepsilon$. This is the upper half of the interval sandwich that proves the creeping bridge: the creeping mass is the drift part of the potential measure, so large-level creeping is controlled above by potential interval masses.
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
/-- Upper sandwich half of the creeping bridge: the creeping probability is eventually at most d/mu + epsilon. -/
theorem creepingProbabilityUpperBoundEventually
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
    creepingProbability P Y death x ≤ d / (∫ omega, Y 1 omega ∂P) + ε := by
  sorry
end Kyprianou.Ch05
