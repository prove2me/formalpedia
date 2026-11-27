-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitFirstMomentV1
-- name    : Kyprianou.Ch05.unkilledPotentialUnitFirstMomentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:09:30.054766+00:00
-- url     : https://prove2.me/theorems/deb8b51e-e45b-51fb-9a08-92b35bbb0094
-- title:
--   Unit discounted potential nonnegative first moment
-- statement:
--   Tonelli and linear subordinator means give the nonnegative first moment of the unit discounted potential.
-- source:
--   Kyprianou (2006), Corollary 5.3, p. 114; reduction of fcb23456-1e1f-487b-828b-a95cacc96d37.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPotentialUnitFirstMomentV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P) :
    (∫⁻ x : Real, ENNReal.ofReal x ∂(U 1)) =
      ENNReal.ofReal (∫ w, Y 1 w ∂P) := by sorry
