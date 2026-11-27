-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingPotentialRatioLimit
-- name    : Kyprianou.Ch05.creepingPotentialRatioLimit
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:48:59.17017+00:00
-- url     : https://prove2.me/theorems/67189d5c-76cb-522c-b9fe-4aafbb1c76a1
-- title:
--   Theorem 5.7 (creeping, positive drift): creeping-to-potential ratio tends to d
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 with positive drift $d>0$, the ratio of the creeping probability at level $x$ to the unit potential interval mass $(U\,0)(x,x+1]$ tends to $d$. This is the potential-density form of creeping: the creeping mass is $d$ times the potential density, and the unit interval mass is the density averaged over a unit window.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121, via Corollary 5.3, p. 114.

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
/-- Positive-drift ratio limit: creeping probability over unit potential interval mass tends to the drift. -/
theorem creepingPotentialRatioLimit
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
  Tendsto (fun x : Real => creepingProbability P Y death x / ((U 0) (Set.Ioc x (x + 1))).toReal) atTop (nhds d) := by
  sorry
end Kyprianou.Ch05
