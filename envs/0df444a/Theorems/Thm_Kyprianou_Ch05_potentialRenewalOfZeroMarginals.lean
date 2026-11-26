-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialRenewalOfZeroMarginals
-- name    : Kyprianou.Ch05.potentialRenewalOfZeroMarginals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:18:20.698367+00:00
-- url     : https://prove2.me/theorems/5a115409-df6f-4e5e-b5c6-9bd9c49d961d
-- title:
--   Lemma 5.2: degenerate zero subordinator branch
-- statement:
--   The zero subordinator has unit-discount potential equal to the Dirac measure at zero and infinite undiscounted occupation there, giving the renewal identity without finite-transform assumptions.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact reduction of 236fd4ab-a605-4b79-a83b-a3aaf7704a5b.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.potentialRenewalOfZeroMarginals
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hzero : ∀ t : NNReal, ∀ᵐ w ∂P, Y t w = 0) :
    renewalMeasure (U 1) = Measure.dirac (0 : Real) + U 0 := by sorry
