-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cosIntegral_eq_exp_mul_cos
-- name    : Kyprianou.Ch05.killedSubordinator_cosIntegral_eq_exp_mul_cos
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T09:25:55.228884+00:00
-- url     : https://prove2.me/theorems/9f49a235-a149-513d-87f5-4ba78a4daf65
-- title:
--   Characteristic function of Y_t from the Laplace law, cosine part
-- statement:
--   Cosine half of the characteristic-function formula for a killed subordinator: the one-dimensional law of $Y_t$ is pinned by its real Laplace transform (hLaplaceLaw) and $Y_t \ge 0$, so $E[\cos(u Y_t)] = \exp(-t R(u)) \cos(t(S(u) + d u))$, where $R(u) = \int (1 - \cos(ux)) \, d\Pi$ and $S(u) = \int \sin(ux) \, d\Pi$ are the real and (negative) imaginary parts of the Levy-Khintchine exponent.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Levy Processes, Chapter 5; cosine half of killedSubordinator_chf_formula (analytic continuation of the Laplace law, eq. (5.1)).

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

/-- Cosine part of the characteristic function of Y_t (analytic continuation of the Laplace law). -/
theorem killedSubordinator_cosIntegral_eq_exp_mul_cos
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
        Real.exp (-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) * Real.cos ((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u))
  := by
  sorry

end Kyprianou.Ch05
