-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_chf_formula
-- name    : Kyprianou.Ch05.killedSubordinator_chf_formula
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T04:10:32.944728+00:00
-- url     : https://prove2.me/theorems/7edcfc5d-c94a-5bcf-9403-b4f9063a13f7
-- title:
--   Characteristic function of Y_t from the Laplace law (analytic continuation)
-- statement:
--   The one-dimensional law of Y_t is pinned by its real Laplace transform (hLaplaceLaw) and Y_t >= 0, so its characteristic function is the infinitely divisible one with the same exponent: E[cos(u Y_t)] = exp(-t R(u)) cos(t(S(u) + d u)) and E[sin(u Y_t)] = exp(-t R(u)) sin(t(S(u) + d u)), where R(u) = int (1 - cos(ux)) dPi is the real part and S(u) = int sin(ux) dPi the (negative) imaginary part of the Levy-Khintchine exponent.
-- source:
--   Kyprianou (2006), Theorem 5.4 decomposition infrastructure: characteristic-function form of the Laplace law hLaplaceLaw.

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

/-- Characteristic function of Y_t from the Laplace law (analytic continuation). -/
theorem killedSubordinator_chf_formula
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
        Real.exp (-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) * Real.cos ((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u)) ∧
    (∫ omega, Real.sin (u * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) * Real.sin ((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u))
  := by
  sorry

end Kyprianou.Ch05
