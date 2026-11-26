-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingLimitFromPotentialLimits
-- name    : Kyprianou.Ch05.creepingLimitFromPotentialLimits
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-26T14:33:07.041802+00:00
-- url     : https://prove2.me/theorems/aff94865-889c-546a-9e87-50c925b9c7df
-- title:
--   Theorem 5.7 (creeping bridge): potential interval limits determine the creeping limit
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, suppose the nonlattice potential interval limits hold: for every $y>0$, $(U\,0)(x,x+y]\to y/\mu$ as $x\to\infty$, where $\mu$ is the finite positive mean. Then the creeping probability at level $x$ converges to $d/\mu$, where $d$ is the drift. This isolates the passage-to-potential bridge step of the creeping part of Theorem 5.7: the creeping mass is the drift part of the potential measure, so the renewal limit for potential intervals transports to the creeping probability.
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
/-- Bridge step for Theorem 5.7 (creeping): the nonlattice potential
interval limits determine the limiting creeping probability. -/
theorem creepingLimitFromPotentialLimits
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
  Tendsto (fun x : Real => creepingProbability P Y death x)
    atTop (nhds (d / (∫ omega, Y 1 omega ∂P))) := by
  sorry
end Kyprianou.Ch05
