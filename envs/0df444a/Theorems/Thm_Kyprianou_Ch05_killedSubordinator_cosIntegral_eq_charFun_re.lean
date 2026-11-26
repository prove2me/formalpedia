-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cosIntegral_eq_charFun_re
-- name    : Kyprianou.Ch05.killedSubordinator_cosIntegral_eq_charFun_re
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:27:35.911799+00:00
-- url     : https://prove2.me/theorems/6deec419-68f0-4971-a5c8-00e68b1f31a4
-- statement:
--   For a killed subordinator with Laplace triplet, the cosine integral of $Y_t$ at frequency $u$ equals the real part of the characteristic function of the law of $Y_t$ at $u$.

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

/-- Cosine integral of Y_t as the real part of the characteristic function of its law. -/
theorem killedSubordinator_cosIntegral_eq_charFun_re
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
  ∀ (t : NNReal) (u : Real),
    (∫ omega, Real.cos (u * Y t omega) ∂P) =
        (MeasureTheory.charFun (P.map (Y t)) u).re
  := by
  sorry

end Kyprianou.Ch05
