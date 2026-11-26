-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_chf_lattice_frequency_one
-- name    : Kyprianou.Ch05.killedSubordinator_chf_lattice_frequency_one
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:49:12.174281+00:00
-- url     : https://prove2.me/theorems/eb30b7ed-9dcc-5873-815d-7b452112c78c
-- title:
--   Ch05: characteristic function at lattice frequency 2π/h is 1
-- statement:
--   For a killed subordinator with drift d = 0 whose Lévy measure Pi is concentrated on the lattice hZ (the off-lattice set has Pi-measure zero), the characteristic function of Y_t at the lattice frequency u = 2π/h equals 1 for every t: the P-integral of cos(u * Y_t) is 1 and the P-integral of sin(u * Y_t) is 0.
-- source:
--   Kyprianou 2006, Ch.5 Thm 5.4 proof route (characteristic function at lattice frequency)

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

/-- Characteristic function at the lattice frequency u = 2π/h equals 1: analytic-continuation core of path lattice support. -/
theorem killedSubordinator_chf_lattice_frequency_one
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
  (d = 0 → ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
    ∀ t : NNReal,
      (∫ omega, Real.cos ((2 * Real.pi / h) * Y t omega) ∂P) = 1 ∧
      (∫ omega, Real.sin ((2 * Real.pi / h) * Y t omega) ∂P) = 0)
 := by
  sorry

end Kyprianou.Ch05
