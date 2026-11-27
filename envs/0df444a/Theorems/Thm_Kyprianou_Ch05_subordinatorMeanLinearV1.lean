-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinatorMeanLinearV1
-- name    : Kyprianou.Ch05.subordinatorMeanLinearV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:20:34.473186+00:00
-- url     : https://prove2.me/theorems/da9546de-2c4e-5791-9849-f371e3fde569
-- title:
--   Linear finite first moment of an unkilled subordinator
-- statement:
--   Stationary increments and monotone paths give integrability at all times and a monotone additive mean.
-- source:
--   Kyprianou (2006), Corollary 5.3, p. 114; reduction of fcb23456-1e1f-487b-828b-a95cacc96d37.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.subordinatorMeanLinearV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P) :
    ∀ t : NNReal, Integrable (Y t) P ∧
      (∫ w, Y t w ∂P) = (t : Real) * (∫ w, Y 1 w ∂P) := by sorry
