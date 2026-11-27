-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingUpperPositiveDrift
-- name    : Kyprianou.Ch05.creepingUpperPositiveDrift
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:37:09.268223+00:00
-- url     : https://prove2.me/theorems/46692f4f-44ac-5458-aeb7-07d1b9d77781
-- title:
--   Theorem 5.7 (creeping upper, positive drift): eventual upper bound when d > 0
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 together with the potential interval limits, in the case of positive drift $d>0$: the creeping probability is eventually at most $d/\mu+\varepsilon$, by the potential interval sandwich (the creeping mass is the drift part of the potential). This is one case of the interval sandwich proving the creeping bridge bound.
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
/-- Case split of the creeping sandwich bound: Theorem 5.7 (creeping upper, positive drift): eventual upper bound when d > 0. -/
theorem creepingUpperPositiveDrift
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
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, creepingProbability P Y death x ≤ d / (∫ omega, Y 1 omega ∂P) + ε := by
  sorry
end Kyprianou.Ch05
