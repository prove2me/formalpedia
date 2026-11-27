-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPassageAlmostSureV1
-- name    : Kyprianou.Ch05.unkilledPassageAlmostSureV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:33:30.409225+00:00
-- url     : https://prove2.me/theorems/21a168f0-44b7-4f4b-b8ea-011897ba8c7a
-- title:
--   Positive mean implies almost sure finite strict passage
-- statement:
--   Positive mean implies almost sure finite strict passage
-- source:
--   Kyprianou (2006), Theorem 5.7; finite-mean passage and creeping reduction.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPassageAlmostSureV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ w, Y 1 w ∂P)
    (x : Real) :
    ∀ᵐ w ∂P, PassageFinite Y death x w := by sorry
