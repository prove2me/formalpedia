-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_atom_sq_le_cesaro_chfAbs
-- name    : Kyprianou.Ch05.killedSubordinator_atom_sq_le_cesaro_chfAbs
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T04:12:49.731008+00:00
-- url     : https://prove2.me/theorems/00aced1d-2af9-47f4-aaab-a365db034e7b
-- title:
--   Wiener bound: atom squared bounded by Cesaro mean of |chf|^2
-- statement:
--   For every t>0, x, and ε>0 there is U0 such that for all U≥U0, P(Y_t = x)^2 ≤ (1/U)∫_0^U [(E cos(uY_t))^2 + (E sin(uY_t))^2] du + ε. Wiener's theorem for the law of Y_t, in |characteristic function|^2 form.
-- source:
--   Kyprianou (2006), Theorem 5.4(i) machinery; Wiener theorem; decomposition child of killedSubordinator_atom_sq_le_cesaro_chf (79640baf).

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

/-- Wiener bound in |chf|^2 form: squared fixed-time atom bounded by Cesaro mean of (Re chf)^2 + (Im chf)^2. -/
theorem killedSubordinator_atom_sq_le_cesaro_chfAbs
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
      (P {omega : Omega | Y t omega = x})^2 ≤ (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫ omega, Real.cos (u * Y t omega) ∂P)^2 + (∫ omega, Real.sin (u * Y t omega) ∂P)^2) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε)
 := by
  sorry

end Kyprianou.Ch05
