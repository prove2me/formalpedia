-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingLowerBackwardWindowBound
-- name    : Kyprianou.Ch05.creepingLowerBackwardWindowBound
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:16:32.306713+00:00
-- url     : https://prove2.me/theorems/58b9a0f3-c2ae-57f3-84bf-5cc8a30c4053
-- title:
--   Theorem 5.7 (creeping lower): bound by the backward potential window
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 with positive drift, for every $\delta>0$ the creeping probability at level $x$ is eventually at least $(d-\delta)$ times the backward unit potential mass $(U\,0)(x-1,x]$. This is the last-exit form of the lower creeping bound.
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
/-- Lower relative creeping bound with the backward unit potential window. -/
theorem creepingLowerBackwardWindowBound
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
  ∀ δ : Real, 0 < δ → ∀ᶠ x : Real in atTop, (d - δ) * ((U 0) (Set.Ioc (x - 1) x)).toReal ≤ creepingProbability P Y death x := by
  sorry
end Kyprianou.Ch05
