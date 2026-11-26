-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_restrictedExponent_bohr_second_moment
-- name    : Kyprianou.Ch05.killedSubordinator_restrictedExponent_bohr_second_moment
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T11:29:25.249607+00:00
-- url     : https://prove2.me/theorems/cc0c56f0-a9a0-5eba-8965-15cfbde52cd2
-- title:
--   Bohr second moment of the restricted characteristic exponent
-- statement:
--   For a killed subordinator with Levy measure $\Pi$ of infinite mass on $(0,\infty)$, the Cesaro mean over $[0,U]$ of the square of the restricted real exponent $\tilde R_\delta(u) = \int_{[\delta,1]} (1-\cos(uy))\,\Pi(dy)$ is eventually at most $\Lambda_\delta^2 + \frac12 A_\delta + \varepsilon$, where $\Lambda_\delta = \Pi([\delta,1])$ and $A_\delta = \sum_{y \in [\delta,1]} \Pi(\{y\})^2$ is the atom-mass sum (written as the integral of $y \mapsto \Pi(\{y\})$ against $\Pi$ on $[\delta,1]$).

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

theorem killedSubordinator_restrictedExponent_bohr_second_moment
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
    ∀ δ : Real, 0 < δ → δ ≤ 1 → ∀ ε : ENNReal, 0 < ε →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)^2) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ENNReal.ofReal ((Pi (Set.Icc δ 1)).toReal^2) + (1/2 : ENNReal) * ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal + ε)
 := by
  sorry

end Kyprianou.Ch05
