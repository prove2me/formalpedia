-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingPotentialDifferenceLimit
-- name    : Kyprianou.Ch05.creepingPotentialDifferenceLimit
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T01:00:43.806827+00:00
-- url     : https://prove2.me/theorems/fcc5ef51-0e6d-5c18-9ecd-8ed5dab32d62
-- title:
--   Theorem 5.7 (creeping, positive drift): creeping minus drift times potential tends to zero
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 with positive drift $d>0$ and the potential interval limits, the difference between the creeping probability at level $x$ and $d$ times the unit potential interval mass $(U\,0)(x,x+1]$ tends to $0$. This is the absolute-error form of the creeping density relation: creeping mass equals drift times potential mass, up to a vanishing error.
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
/-- Positive-drift difference form of creeping: creeping probability minus
drift times unit potential interval mass tends to zero. -/
theorem creepingPotentialDifferenceLimit
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
  Tendsto (fun x : Real => creepingProbability P Y death x - d * ((U 0) (Set.Ioc x (x + 1))).toReal)
    atTop (nhds 0) := by
  sorry
end Kyprianou.Ch05
