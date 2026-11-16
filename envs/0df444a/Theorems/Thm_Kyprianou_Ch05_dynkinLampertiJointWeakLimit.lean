-- Prove2me | Theorems.Thm_Kyprianou_Ch05_dynkinLampertiJointWeakLimit
-- name    : Kyprianou.Ch05.dynkinLampertiJointWeakLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:54:33.2028+00:00
-- url     : https://prove2.me/theorems/7fa1c751-9b5f-4ceb-b829-29c7cd4dfd33
-- title:
--   Theorem 5.16: two-dimensional Dynkin-Lamperti asymptotics
-- statement:
--   For alpha strictly between zero and one, if Phi varies regularly at zero then x->infinity, or if Phi varies regularly at infinity then x->0+, the entire rescaled overshoot/undershoot pair converges weakly to the density alpha*sin(pi*alpha)/pi (1-y)^(alpha-1)(y+u)^(-alpha-1) on u>0, y in [0,1).
-- source:
--   Kyprianou (2006), first edition, result 5.16, printed pages 121, 130 or 132.

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

/-- Theorem 5.16, p.130: two-dimensional Dynkin-Lamperti weak convergence
with exact alpha*sin(pi*alpha)/pi density and correct endpoint regimes. -/
theorem dynkinLampertiJointWeakLimit
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
    (alpha : Real) (hAlpha : 0 < alpha ∧ alpha < 1)
    (hRV : RegularlyVaryingAtZero Phi alpha ∨
            RegularlyVaryingAtInfinity Phi alpha) :
  ((RegularlyVaryingAtZero Phi alpha →
     ∀ f : Real × Real → Real, IsBoundedContinuousTest f →
       Tendsto
         (fun x : Real => scaledPassageTestExpectation P Y Yleft death x f)
         atTop (nhds (dynkinLampertiTestIntegral alpha f))) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ∀ f : Real × Real → Real, IsBoundedContinuousTest f →
       Tendsto
         (fun x : Real => scaledPassageTestExpectation P Y Yleft death x f)
         (nhdsWithin (0 : Real) (Set.Ioi 0))
         (nhds (dynkinLampertiTestIntegral alpha f))))
 := by
  sorry

end Kyprianou.Ch05
