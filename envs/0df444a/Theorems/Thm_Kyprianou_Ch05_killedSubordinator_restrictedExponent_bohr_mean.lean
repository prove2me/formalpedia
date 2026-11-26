-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_restrictedExponent_bohr_mean
-- name    : Kyprianou.Ch05.killedSubordinator_restrictedExponent_bohr_mean
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:29:20.849679+00:00
-- url     : https://prove2.me/theorems/0a70f0ec-74e8-578c-9921-63c061541f58
-- title:
--   Bohr mean of the restricted characteristic exponent
-- statement:
--   For a killed subordinator with Levy measure $\Pi$ of infinite mass on $(0,\infty)$ and triplet $(\eta, d, \Pi)$, the Cesaro mean over $[0,U]$ of the restricted real exponent $\tilde R_\delta(u) = \int_{[\delta,1]} (1-\cos(uy))\,\Pi(dy)$ converges to the mass $\Lambda_\delta = \Pi([\delta,1])$ as $U \to \infty$: for every $\varepsilon > 0$ there is $U_0$ such that for all $U \ge U_0$ the Cesaro mean differs from $\Lambda_\delta$ by at most $\varepsilon$ (two-sided).

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

theorem killedSubordinator_restrictedExponent_bohr_mean
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
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ENNReal.ofReal (Pi (Set.Icc δ 1)).toReal + ε ∧
        ENNReal.ofReal (Pi (Set.Icc δ 1)).toReal ≤ (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε)
 := by
  sorry

end Kyprianou.Ch05
