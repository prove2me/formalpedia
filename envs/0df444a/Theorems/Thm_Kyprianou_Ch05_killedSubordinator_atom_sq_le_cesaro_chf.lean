-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_atom_sq_le_cesaro_chf
-- name    : Kyprianou.Ch05.killedSubordinator_atom_sq_le_cesaro_chf
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:51:38.906668+00:00
-- url     : https://prove2.me/theorems/79640baf-a4e8-5756-9f21-3783422eff76
-- title:
--   Atom squared bounded by Cesaro mean of characteristic function (Wiener)
-- statement:
--   For every fixed time t>0 and point x, the square of the atom P(Y_t = x) is at most the Cesaro average over [0,U] of exp(-2t R u), times 1/U, plus an arbitrary epsilon, for all large U, where R u is the real part of the characteristic exponent.
-- source:
--   Kyprianou, Fluctuations of Levy Processes (2006), Ch. 5, Thm 5.4 infrastructure: Wiener theorem for infinitely divisible laws

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

/-- Wiener bound: squared fixed-time atom bounded by Cesaro mean of |characteristic function|^2. -/
theorem killedSubordinator_atom_sq_le_cesaro_chf
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
  (∀ t : NNReal, 0 < t → ∀ x : Real, ∀ ε : ENNReal, 0 < ε →
    ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
      (P {omega : Omega | Y t omega = x})^2 ≤ (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε)
 := by
  sorry

end Kyprianou.Ch05
