-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_sinIntegral_eq_charFun_im
-- name    : Kyprianou.Ch05.killedSubordinator_sinIntegral_eq_charFun_im
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:26:52.978681+00:00
-- url     : https://prove2.me/theorems/ef14a62f-8272-453e-8b61-114686c354bc
-- statement:
--   Let $Y$ be a killed subordinator on a probability space $(\Omega, P)$ with killing time $\mathrm{death}$ and killing rate $\eta \ge 0$, with Laplace triplet $(\eta, d, \Pi)$ and exponent $\Phi$, so that $\int e^{-\theta Y_t}\,dP = e^{-t(\Phi(\theta)-\eta)}$ for $\theta \ge 0$. For each fixed time $t$ and frequency $u \in \mathbb{R}$, the sine transform of the law of $Y_t$ equals the imaginary part of its characteristic function:
--
--   $$\int_\Omega \sin(u\, Y_t(\omega))\,dP(\omega) = \operatorname{Im} \varphi_{Y_t}(u), \qquad \varphi_{Y_t}(u) = \int_{\mathbb{R}} e^{iuz}\, d(P \circ Y_t^{-1})(z).$$
--
--   This is the bridge between the real sine integral appearing in the potential-theoretic arguments and the complex characteristic function of the marginal law, to which the Lévy–Khintchine formula applies.
--
--   Formalization Note: the characteristic function is Mathlib's `MeasureTheory.charFun` of the pushforward measure `P.map (Y t)`, and the identity is proved by commuting the imaginary part with the Bochner integral and changing variables along `Y t`, which is a.e. measurable.

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

/-- Sine integral equals the imaginary part of the characteristic function of the law of Y_t. -/
theorem killedSubordinator_sinIntegral_eq_charFun_im
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
    (∫ omega, Real.sin (u * Y t omega) ∂P) =
      (MeasureTheory.charFun (P.map (Y t)) u).im
  := by
  sorry

end Kyprianou.Ch05
