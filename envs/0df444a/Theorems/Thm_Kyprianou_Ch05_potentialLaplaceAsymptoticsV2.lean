-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialLaplaceAsymptoticsV2
-- name    : Kyprianou.Ch05.potentialLaplaceAsymptoticsV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:36:40.846255+00:00
-- url     : https://prove2.me/theorems/0874d7ec-ec29-4b22-a4a3-0872819493a3
-- title:
--   potentialLaplaceAsymptotics (corrected reciprocal factor)
-- statement:
--   Use the slowly varying factor L of the reciprocal exponent, so Phi(1/x) = x^(-rho)/L(x). The potential transform and cumulative asymptotic then use L multiplicatively.
-- source:
--   Kyprianou (2006), Lemma 5.17, corrected reciprocal factor.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Corrected reciprocal slowly varying factor for the potential measure. -/
theorem potentialLaplaceAsymptoticsV2
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1) :
  ((RegularlyVaryingAtZero Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtInfinity L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) / L x) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace (U 0) theta).toReal /
             (theta ^ (-alpha) * L (1 / theta)))
         (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtZero L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) / L x) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace (U 0) theta).toReal /
             (theta ^ (-alpha) * L (1 / theta)))
         atTop (nhds 1))) := by
  sorry

end Kyprianou.Ch05
