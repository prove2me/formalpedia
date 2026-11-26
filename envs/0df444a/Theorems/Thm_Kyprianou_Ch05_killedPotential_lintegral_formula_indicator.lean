-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_lintegral_formula_indicator
-- name    : Kyprianou.Ch05.killedPotential_lintegral_formula_indicator
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T10:05:43.969804+00:00
-- url     : https://prove2.me/theorems/333471fa-ac2f-4403-8cf8-1e7016dbf179
-- title:
--   Occupation formula for indicator functions
-- statement:
--   For a killed subordinator with $q$-potential family $U^q$, the occupation formula holds for indicator functions: integrating $c \cdot 1_B$ against $U^q$ equals the discounted time-integral of $c$ times the probability of being alive at time $t$ with $Y_t \in B$.
-- source:
--   Kyprianou (2006), Ch. 5, Thm 5.4 proof infrastructure (decomposition child: indicator case of the Tonelli occupation formula).

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

/-- The occupation formula for indicator functions: the indicator case of the
Tonelli form of the killed potential. -/
theorem killedPotential_lintegral_formula_indicator
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
  ∀ q : Real, 0 ≤ q → ∀ (c : ENNReal) (B : Set Real), MeasurableSet B →
      (∫⁻ x : Real, B.indicator (fun _ => c) x ∂(U q)) =
        ∫⁻ t in Set.Ici (0 : Real),
          ENNReal.ofReal (Real.exp (-q * t)) *
          ∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            B.indicator (fun _ => c) (Y (Real.toNNReal t) omega) ∂P ∂volume
 := by
  sorry

end Kyprianou.Ch05
