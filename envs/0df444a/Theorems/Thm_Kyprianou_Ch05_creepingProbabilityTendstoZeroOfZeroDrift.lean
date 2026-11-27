-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingProbabilityTendstoZeroOfZeroDrift
-- name    : Kyprianou.Ch05.creepingProbabilityTendstoZeroOfZeroDrift
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:48:54.412428+00:00
-- url     : https://prove2.me/theorems/41c5d4e3-f357-516b-b6f5-83ef2fa01901
-- title:
--   Theorem 5.7 (creeping, zero drift): creeping probability tends to zero
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 with zero drift $d=0$, the creeping probability tends to $0$ as the level grows. With no drift, continuous crossing is impossible, and under the nonlattice hypothesis the probability of a jump landing exactly on the level also vanishes in the limit.
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
/-- Zero-drift creeping limit: the creeping probability tends to zero. -/
theorem creepingProbabilityTendstoZeroOfZeroDrift
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
    (hd : d = 0) :
  Tendsto (fun x : Real => creepingProbability P Y death x) atTop (nhds 0) := by
  sorry
end Kyprianou.Ch05
