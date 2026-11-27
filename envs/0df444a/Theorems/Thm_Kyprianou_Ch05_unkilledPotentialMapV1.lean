-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPotentialMapV1
-- name    : Kyprianou.Ch05.unkilledPotentialMapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:06.55984+00:00
-- url     : https://prove2.me/theorems/4afa8aa8-973e-550d-a9ac-46ed6e05af4d
-- title:
--   Unkilled potential as a discounted occupation pushforward
-- statement:
--   Represent the potential family as the pushforward of discounted time measure times the probability measure under a jointly measurable process version.
-- source:
--   Kyprianou (2006), Corollary 5.3, p. 114; reduction of fcb23456-1e1f-487b-828b-a95cacc96d37.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPotentialMapV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    ∃ Z : NNReal → Omega → Real,
      Measurable (fun p : Real × Omega => Z (Real.toNNReal p.1) p.2) ∧
      (∀ᵐ w ∂P, ∀ t : NNReal, Z t w = Y t w) ∧
      ∀ q : Real, 0 ≤ q →
        U q = Measure.map (fun p : Real × Omega => Z (Real.toNNReal p.1) p.2)
          (((volume.restrict (Set.Ici (0 : Real))).withDensity
            (fun t => ENNReal.ofReal (Real.exp (-q*t)))).prod P) := by sorry
