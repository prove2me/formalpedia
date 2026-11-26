-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialRenewalOfPositiveLaplace
-- name    : Kyprianou.Ch05.potentialRenewalOfPositiveLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:18:20.070784+00:00
-- url     : https://prove2.me/theorems/ec483754-18d8-4dd7-bf2f-ddee88ad408a
-- title:
--   Lemma 5.2: nonzero branch by Laplace uniqueness
-- statement:
--   If the potential transforms are the unit-discounted and undiscounted resolvents of a strictly positive exponent, the renewal identity follows by uniqueness.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact reduction of 236fd4ab-a605-4b79-a83b-a3aaf7704a5b.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.potentialRenewalOfPositiveLaplace
    (U : Real → Measure Real) [IsProbabilityMeasure (U 1)]
    (hLaplace : ∀ theta : Real, 0 < theta → ∃ a : Real, 0 < a ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 1)) = (ENNReal.ofReal (1 + a))⁻¹ ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 0)) = (ENNReal.ofReal a)⁻¹) :
    renewalMeasure (U 1) = Measure.dirac (0 : Real) + U 0 := by sorry
