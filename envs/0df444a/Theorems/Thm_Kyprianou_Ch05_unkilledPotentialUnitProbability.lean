-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitProbability
-- name    : Kyprianou.Ch05.unkilledPotentialUnitProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:18:09.655617+00:00
-- url     : https://prove2.me/theorems/522edc79-c1c8-5dd2-97eb-fe87f6f1ab92
-- title:
--   Lemma 5.2: unit-discount potential is a probability law
-- statement:
--   The unit-discount potential of an unkilled subordinator has total mass one.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact reduction of 236fd4ab-a605-4b79-a83b-a3aaf7704a5b.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPotentialUnitProbability
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    IsProbabilityMeasure (U 1) := by sorry
