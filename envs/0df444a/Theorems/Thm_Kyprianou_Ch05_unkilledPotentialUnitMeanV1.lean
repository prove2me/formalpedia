-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitMeanV1
-- name    : Kyprianou.Ch05.unkilledPotentialUnitMeanV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:20:28.68897+00:00
-- url     : https://prove2.me/theorems/facc5444-bc3b-4e87-a757-4e7a3fe129aa
-- title:
--   Mean of the unit-discount potential
-- statement:
--   Integrating the linear mean against the unit exponential occupation weighting gives the same finite first moment.
-- source:
--   Kyprianou (2006), Corollary 5.3, p. 114; reduction of fcb23456-1e1f-487b-828b-a95cacc96d37.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPotentialUnitMeanV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P) :
    Integrable (fun x : Real => x) (U 1) ∧
      (∫ x : Real, x ∂(U 1)) = (∫ w, Y 1 w ∂P) := by sorry
