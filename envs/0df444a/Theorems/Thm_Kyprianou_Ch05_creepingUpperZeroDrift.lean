-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingUpperZeroDrift
-- name    : Kyprianou.Ch05.creepingUpperZeroDrift
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:37:20.252426+00:00
-- url     : https://prove2.me/theorems/f44ebf1e-087a-5305-b59c-475c99ad8c73
-- title:
--   Theorem 5.7 (creeping upper, zero drift): eventual upper bound when d = 0
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 together with the potential interval limits, in the case of zero drift $d=0$: under the nonlattice hypothesis, exact jump landings on the level have vanishing probability, so the creeping probability is eventually at most $\varepsilon$. This is one case of the interval sandwich proving the creeping bridge bound.
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
/-- Case split of the creeping sandwich bound: Theorem 5.7 (creeping upper, zero drift): eventual upper bound when d = 0. -/
theorem creepingUpperZeroDrift
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
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, creepingProbability P Y death x ≤ d / (∫ omega, Y 1 omega ∂P) + ε := by
  sorry
end Kyprianou.Ch05
