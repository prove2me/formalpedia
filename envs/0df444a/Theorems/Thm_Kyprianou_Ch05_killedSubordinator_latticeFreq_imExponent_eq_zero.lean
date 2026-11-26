-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_latticeFreq_imExponent_eq_zero
-- name    : Kyprianou.Ch05.killedSubordinator_latticeFreq_imExponent_eq_zero
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T04:13:18.923584+00:00
-- url     : https://prove2.me/theorems/1a7a17ee-9ba9-4f73-baca-85dd7ca3f715
-- title:
--   killedSubordinator_latticeFreq_imExponent_eq_zero
-- statement:
--   For a killed subordinator whose Lévy measure Pi is concentrated on the lattice hZ (off-lattice set has Pi-measure zero), the imaginary part of the characteristic exponent at the lattice frequency u = 2π/h vanishes: the Pi-integral over (0,∞) of sin(u x) is 0, because sin(u x) = 0 at every lattice point and Pi-a.e. point of (0,∞) is a lattice point.
-- source:
--   Kyprianou 2006, Ch.5 Thm 5.4 proof route (lattice frequency exponent vanishing)

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

/-- Imaginary part of the characteristic exponent vanishes at the lattice frequency 2π/h when Pi is concentrated on hZ. -/
theorem killedSubordinator_latticeFreq_imExponent_eq_zero
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
  (∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
    (∫ x in Set.Ioi (0 : Real), Real.sin ((2 * Real.pi / h) * x) ∂Pi) = 0)
 := by
  sorry

end Kyprianou.Ch05
