-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingDifferenceLowerBound
-- name    : Kyprianou.Ch05.creepingDifferenceLowerBound
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T01:08:40.176248+00:00
-- url     : https://prove2.me/theorems/f84e0ff6-df9c-5585-919c-2614c7205756
-- title:
--   Theorem 5.7 (creeping difference, lower): creeping is eventually at least drift times potential minus epsilon
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 with positive drift, the creeping probability at level $x$ is eventually at least $d$ times the unit potential interval mass $(U\,0)(x,x+1]$ minus $\varepsilon$: the difference $\mathrm{creep}(x) - d\,U(x,x+1]$ is eventually above $-\varepsilon$. This is the lower half of the creeping density relation.
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
/-- Lower epsilon half of the creeping difference limit. -/
theorem creepingDifferenceLowerBound
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
        atTop (nhds (y / (∫ omega, Y 1 omega ∂P))))
    (hd : 0 < d) :
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, -ε ≤ creepingProbability P Y death x - d * ((U 0) (Set.Ioc x (x + 1))).toReal := by
  sorry
end Kyprianou.Ch05
