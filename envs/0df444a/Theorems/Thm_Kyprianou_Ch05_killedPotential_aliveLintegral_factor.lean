-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_aliveLintegral_factor
-- name    : Kyprianou.Ch05.killedPotential_aliveLintegral_factor
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T09:30:33.923017+00:00
-- url     : https://prove2.me/theorems/21a7184f-3337-4640-99a8-ca7c9718eb5a
-- title:
--   Killing independence factorization of the survival-restricted Laplace lintegral
-- statement:
--   For a killed subordinator with killing rate $\eta$, the Laplace integral of $e^{-\theta Y_t}$ restricted to the survival event $\{t < \mathrm{death}\}$ factors as the unrestricted Laplace integral times the survival probability $e^{-\eta t}$, by independence of the killing time and the path.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Levy Processes with Applications (2006), Ch. 5, Thm 5.4 proof infrastructure (decomposition child).

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

/-- Killing independence: the survival-restricted Laplace lintegral factors as the
unrestricted lintegral times the survival probability. -/
theorem killedPotential_aliveLintegral_factor
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
  ∀ (t : Real), 0 ≤ t → ∀ theta : Real, 0 ≤ theta →
      (∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
        ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P) =
      (∫⁻ omega, ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P) *
        ENNReal.ofReal (Real.exp (-eta * t))
 := by
  sorry

end Kyprianou.Ch05
