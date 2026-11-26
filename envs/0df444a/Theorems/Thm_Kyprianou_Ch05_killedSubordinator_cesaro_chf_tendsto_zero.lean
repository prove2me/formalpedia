-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cesaro_chf_tendsto_zero
-- name    : Kyprianou.Ch05.killedSubordinator_cesaro_chf_tendsto_zero
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:51:42.874994+00:00
-- url     : https://prove2.me/theorems/84725646-d8a7-448b-9a65-f2b14745954f
-- title:
--   Cesaro mean of characteristic decay tends to zero under infinite activity
-- statement:
--   If Pi(0,infty)=top (infinite activity) then for every t>0 and epsilon>0, the Cesaro average over [0,U] of exp(-2t R u), times 1/U, is at most epsilon for all large U.
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

/-- Infinite activity forces the Cesaro mean of exp(-2t Re psi(u)) to vanish as U grows. -/
theorem killedSubordinator_cesaro_chf_tendsto_zero
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
  (Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ t : NNReal, 0 < t → ∀ ε : ENNReal, 0 < ε →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U → (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ε)
 := by
  sorry

end Kyprianou.Ch05
