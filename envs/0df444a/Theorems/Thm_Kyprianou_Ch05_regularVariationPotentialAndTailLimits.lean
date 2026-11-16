-- Prove2me | Theorems.Thm_Kyprianou_Ch05_regularVariationPotentialAndTailLimits
-- name    : Kyprianou.Ch05.regularVariationPotentialAndTailLimits
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:54:56.05452+00:00
-- url     : https://prove2.me/theorems/b5531b22-9033-46a2-afce-fe142dd157ec
-- title:
--   Lemma 5.17: potential-mass and Levy-tail limits at both endpoints
-- statement:
--   For alpha in [0,1] and Phi regularly varying at zero or infinity, U([0,lambda*x])*Phi(1/x) tends to lambda^alpha/Gamma(1+alpha); when alpha<1 the jump tail Pi((lambda*x,infinity))/Phi(1/x) tends to lambda^(-alpha)/Gamma(1-alpha), with x->infinity for Phi at zero and x->0+ for Phi at infinity.
-- source:
--   Kyprianou (2006), first edition, result 5.17, printed pages 121, 130 or 132.

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

/-- Lemma 5.17, p.132, both regimes and both numbered conclusions;
the Levy tail result includes alpha=0 and excludes alpha=1. -/
theorem regularVariationPotentialAndTailLimits
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
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hRV : RegularlyVaryingAtZero Phi alpha ∨
            RegularlyVaryingAtInfinity Phi alpha) :
  ((RegularlyVaryingAtZero Phi alpha →
     ((∀ lambda : Real, 0 < lambda →
        Tendsto
          (fun x : Real =>
            ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
              Phi (1 / x))
          atTop
          (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) ∧
      (alpha < 1 →
        ∀ lambda : Real, 0 < lambda →
          Tendsto
            (fun x : Real =>
              (Pi (Set.Ioi (lambda*x))).toReal / Phi (1 / x))
            atTop
            (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha)))))) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ((∀ lambda : Real, 0 < lambda →
        Tendsto
          (fun x : Real =>
            ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
              Phi (1 / x))
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) ∧
      (alpha < 1 →
        ∀ lambda : Real, 0 < lambda →
          Tendsto
            (fun x : Real =>
              (Pi (Set.Ioi (lambda*x))).toReal / Phi (1 / x))
            (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha)))))))
 := by
  sorry

end Kyprianou.Ch05
