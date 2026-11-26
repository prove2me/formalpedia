-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_inner_aemeasurable
-- name    : Kyprianou.Ch05.killedPotential_inner_aemeasurable
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T10:05:43.773812+00:00
-- url     : https://prove2.me/theorems/88cda105-0c0e-43f6-99a3-3f658893f718
-- title:
--   AE measurability in time of the inner occupation integral
-- statement:
--   For every measurable $f : \mathbb{R} \to [0,\infty]$, the inner occupation integral $t \mapsto \int_{\{t < \mathrm{death}\}} f(Y_t)\,dP$ is almost everywhere measurable with respect to Lebesgue measure on $[0,\infty)$. This is the joint-measurability input (via cadlag paths) needed for the Tonelli form of the killed potential.
-- source:
--   Kyprianou (2006), Ch. 5, Thm 5.4 proof infrastructure (decomposition child: time-measurability of the inner occupation integral).

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- The inner occupation integral, as a function of time, is almost everywhere
measurable with respect to Lebesgue measure on the half-line. -/
theorem killedPotential_inner_aemeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  ∀ f : Real → ENNReal, Measurable f →
    AEMeasurable (fun t : Real =>
      ∫⁻ omega in {omega : Omega |
        (Real.toNNReal t : WithTop NNReal) < death omega},
        f (Y (Real.toNNReal t) omega) ∂P) (volume.restrict (Set.Ici (0 : Real)))
 := by
  sorry

end Kyprianou.Ch05
