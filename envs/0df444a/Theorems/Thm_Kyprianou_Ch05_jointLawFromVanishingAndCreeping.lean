-- Prove2me | Theorems.Thm_Kyprianou_Ch05_jointLawFromVanishingAndCreeping
-- name    : Kyprianou.Ch05.jointLawFromVanishingAndCreeping
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:37:12.963789+00:00
-- url     : https://prove2.me/theorems/1b06b969-f53f-5101-b47c-083cdf1856b4
-- title:
--   Theorem 5.7 (joint law, assembly): vanishing case plus creeping give the joint limit
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, suppose the joint-law limit holds for all bounded continuous tests vanishing at $(0,0)$ (jump term only), and the creeping probability converges to $d/\mu$. Then the full joint-law limit holds for all bounded continuous tests, with limit $\frac{d}{\mu}f(0,0)$ plus the jump term. This isolates the assembly step of Theorem 5.7: a general test is split into its value at the origin (carried by the creeping atom) and a vanishing test (carried by the jump part).
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
/-- Assembly step for Theorem 5.7: the vanishing-test limit and the creeping limit imply the full joint-law limit. -/
theorem jointLawFromVanishingAndCreeping
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
    (hVan : ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
     Tendsto (fun x : Real => passageTestExpectation P Y Yleft death x f) atTop
       (nhds ((1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume))))
    (hCreep : Tendsto (fun x : Real => creepingProbability P Y death x) atTop (nhds (d / (∫ omega, Y 1 omega ∂P)))) :
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f →
     Tendsto (fun x : Real => passageTestExpectation P Y Yleft death x f) atTop
       (nhds (d / (∫ omega, Y 1 omega ∂P) * f (0, 0) + (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume))) := by
  sorry
end Kyprianou.Ch05
