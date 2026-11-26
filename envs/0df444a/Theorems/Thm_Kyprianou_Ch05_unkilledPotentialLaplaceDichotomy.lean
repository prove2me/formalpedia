-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPotentialLaplaceDichotomy
-- name    : Kyprianou.Ch05.unkilledPotentialLaplaceDichotomy
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:18:17.010406+00:00
-- url     : https://prove2.me/theorems/cbe8356f-6685-46d0-bf57-78977a3b6679
-- title:
--   Lemma 5.2: unkilled potential transform dichotomy
-- statement:
--   Either the unkilled subordinator is zero almost surely at each deterministic time, or its discounted and undiscounted potential transforms have a common strictly positive Laplace exponent at every positive argument.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact reduction of 236fd4ab-a605-4b79-a83b-a3aaf7704a5b.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPotentialLaplaceDichotomy
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    (∀ t : NNReal, ∀ᵐ w ∂P, Y t w = 0) ∨
      (∀ theta : Real, 0 < theta → ∃ a : Real, 0 < a ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 1)) = (ENNReal.ofReal (1 + a))⁻¹ ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 0)) = (ENNReal.ofReal a)⁻¹) := by sorry
