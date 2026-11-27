-- Prove2me | Theorems.Thm_Kyprianou_Ch05_jointLawVanishingTestLimit
-- name    : Kyprianou.Ch05.jointLawVanishingTestLimit
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:37:12.226122+00:00
-- url     : https://prove2.me/theorems/166e3b04-492e-595c-8eee-d081413d1616
-- title:
--   Theorem 5.7 (joint law, vanishing tests): jump-part weak limit
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, for every bounded continuous test $f$ with $f(0,0)=0$, the joint passage test expectation converges to the jump term $\frac{1}{\mu}\int_0^\infty\int_y^\infty f(z-y,y)\,\Pi(dz)\,dy$ only: the creeping atom contributes nothing because the test vanishes at $(0,0)$. This is the jump part of Theorem 5.7, driven by the key renewal theorem through the potential family.
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
/-- Joint-law limit for tests vanishing at the origin: only the jump term survives. -/
theorem jointLawVanishingTestLimit
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
    (hNonLattice : NonLatticeMeasure (U 0)) :
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
     Tendsto (fun x : Real => passageTestExpectation P Y Yleft death x f) atTop
       (nhds ((1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume))) := by
  sorry
end Kyprianou.Ch05
