-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_charFun_re_eq_exp_mul_cos
-- name    : Kyprianou.Ch05.killedSubordinator_charFun_re_eq_exp_mul_cos
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:27:57.496663+00:00
-- url     : https://prove2.me/theorems/e87dea02-15e7-5cb0-abee-b8b5a3d62a40
-- statement:
--   The real part of the characteristic function of the law of $Y_t$ at frequency $u$ equals $\exp(-t\,\tilde R(u))\cos(t\,(S(u)+du))$, where $\tilde R$ and $S$ are the real and imaginary parts of the Lévy–Khintchine exponent of the triplet.

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

/-- Real part of the characteristic function of the law of Y_t: exponential-cosine form (exponent identification). -/
theorem killedSubordinator_charFun_re_eq_exp_mul_cos
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
    (MeasureTheory.charFun (P.map (Y t)) u).re =
       Real.exp (-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) * Real.cos ((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u))
  := by
  sorry

end Kyprianou.Ch05
