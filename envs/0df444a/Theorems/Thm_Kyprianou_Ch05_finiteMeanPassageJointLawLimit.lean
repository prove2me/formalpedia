-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finiteMeanPassageJointLawLimit
-- name    : Kyprianou.Ch05.finiteMeanPassageJointLawLimit
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-26T03:07:28.209226+00:00
-- url     : https://prove2.me/theorems/01400b53-f270-4c29-9509-29f09ab72629
-- title:
--   Theorem 5.7 (joint law): finite-mean weak limit of overshoot and undershoot
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 (killed subordinator, finite positive mean $\mu$, nonlattice potential), for every bounded continuous test $f$ the joint passage test expectation converges as $x\to\infty$ to $\frac{d}{\mu} f(0,0) + \frac{1}{\mu}\int_0^\infty\int_y^\infty f(z-y,y)\,\Pi(dz)\,dy$: the creeping atom $d/\mu$ at $(0,0)$ plus the jump intensity term.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121 (joint-law conjunct).

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
/-- Theorem 5.7, joint-law conjunct: weak limit of the joint overshoot/undershoot law. -/
theorem finiteMeanPassageJointLawLimit
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
  let mu : Real := ∫ omega, Y 1 omega ∂P
  (∀ f : Real × Real → Real, IsBoundedContinuousTest f →
     Tendsto
       (fun x : Real => passageTestExpectation P Y Yleft death x f)
       atTop
       (nhds
         (d / mu * f (0,0) +
           (1 / mu) *
             (∫ y in Set.Ici (0 : Real),
                ∫ z in Set.Ioi y, f (z-y,y) ∂Pi ∂volume)))) := by
  sorry
end Kyprianou.Ch05
