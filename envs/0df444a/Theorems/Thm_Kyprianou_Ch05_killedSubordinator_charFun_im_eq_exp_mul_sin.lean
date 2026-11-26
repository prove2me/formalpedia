-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_charFun_im_eq_exp_mul_sin
-- name    : Kyprianou.Ch05.killedSubordinator_charFun_im_eq_exp_mul_sin
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:26:52.273861+00:00
-- url     : https://prove2.me/theorems/42475407-875c-5f33-a8a4-c8525eb5fddd
-- statement:
--   Let $Y$ be a killed subordinator on a probability space $(\Omega, P)$ with Laplace triplet $(\eta, d, \Pi)$ and exponent $\Phi$, so that $\int e^{-\theta Y_t}\,dP = e^{-t(\Phi(\theta)-\eta)}$ for $\theta \ge 0$. Write $\widetilde R(u) = \int_{(0,\infty)} (1 - \cos(ux))\,\Pi(dx)$ for the real part of the characteristic exponent and $S(u) = \int_{(0,\infty)} \sin(ux)\,\Pi(dx)$ for its truncated imaginary part. Then the imaginary part of the characteristic function of $Y_t$ is
--
--   $$\operatorname{Im} \varphi_{Y_t}(u) = e^{-t \widetilde R(u)} \sin\big(t\,(S(u) + d\,u)\big).$$
--
--   This is the sine half of the Lévy–Khintchine formula for the marginal law of a killed subordinator: the analytic continuation of the Laplace law from the positive real axis to the imaginary axis.
--
--   Formalization Note: the characteristic function is Mathlib's `MeasureTheory.charFun` of `P.map (Y t)`; the real part $\widetilde R(u)$ is written through the Lebesgue integral of $1 - \cos(ux)$ against $\Pi$ converted to a real number.

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

/-- Imaginary part of the characteristic function of the law of Y_t in Levy-Khintchine form (sine half). -/
theorem killedSubordinator_charFun_im_eq_exp_mul_sin
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
    (MeasureTheory.charFun (P.map (Y t)) u).im =
        Real.exp (-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) * Real.sin ((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u))
  := by
  sorry

end Kyprianou.Ch05
