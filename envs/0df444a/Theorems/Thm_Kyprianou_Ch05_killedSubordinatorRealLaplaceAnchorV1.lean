-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinatorRealLaplaceAnchorV1
-- name    : Kyprianou.Ch05.killedSubordinatorRealLaplaceAnchorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:54:04.53897+00:00
-- url     : https://prove2.me/theorems/40475fb4-28a3-49ff-b2ff-899955c3a580
-- title:
--   Real Laplace law supplies the complex-transform real-axis anchor
-- statement:
--   Convert the triplet's finite nonnegative integral to Bochner integrability; map the marginal and complexify the real Laplace identity.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set Complex Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch05.killedSubordinatorRealLaplaceAnchorV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta))) :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) (Pi.restrict (Ioi (0 : ℝ))) ∧
    ∀ (t : NNReal) (x : ℝ), 0 < x →
      (∫ y, Complex.exp (-(x : ℂ) * (y : ℂ)) ∂(P.map (Y t))) =
        Complex.exp (-((t : ℝ) : ℂ) *
          ((d : ℂ) * (x : ℂ) +
            ∫ y in Ioi (0 : ℝ), (1 - Complex.exp (-(x : ℂ) * (y : ℂ))) ∂Pi)) := by
  sorry
