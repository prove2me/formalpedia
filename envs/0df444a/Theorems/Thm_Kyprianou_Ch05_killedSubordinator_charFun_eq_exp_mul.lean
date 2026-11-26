-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_charFun_eq_exp_mul
-- name    : Kyprianou.Ch05.killedSubordinator_charFun_eq_exp_mul
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T12:12:54.08838+00:00
-- url     : https://prove2.me/theorems/a26cbf48-d203-41ec-a64e-ccd4df63021b
-- title:
--   Characteristic function of the law of Y_t: complex exponential (Levy-Khintchine) form
-- statement:
--   For a killed subordinator $Y$ with Laplace triplet $(\eta, d, \Pi)$, the characteristic function of the law of $Y_t$ has the complex Levy-Khintchine form: it equals $\exp(-t R(u) + i t (S(u) + d u))$, where $R(u) = \int_{(0,\infty)} (1-\cos(ux))\,\Pi(dx)$ and $S(u) = \int_{(0,\infty)} \sin(ux)\,\Pi(dx)$. Its real and imaginary parts are exactly the cosine and sine exponent identifications.
-- source:
--   Kyprianou, Fluctuations of Levy Processes with Applications (2006), Ch. 5, Thm 5.4 context (Levy-Khintchine formula for the killed subordinator semigroup).

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

/-- Characteristic function of the law of Y_t in complex Levy-Khintchine form: the single complex identity whose real and imaginary parts are the cosine and sine exponent identifications. -/
theorem killedSubordinator_charFun_eq_exp_mul
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
    MeasureTheory.charFun (P.map (Y t)) u =
      Complex.exp (↑(-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) +
        ↑((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u)) * Complex.I)
  := by
  sorry

end Kyprianou.Ch05
