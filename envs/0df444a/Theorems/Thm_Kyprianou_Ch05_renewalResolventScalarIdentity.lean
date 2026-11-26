-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalResolventScalarIdentity
-- name    : Kyprianou.Ch05.renewalResolventScalarIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:18:21.086684+00:00
-- url     : https://prove2.me/theorems/7d4a1d90-bc2e-57e9-bb12-bd782303afbf
-- title:
--   Lemma 5.2: scalar geometric resolvent identity
-- statement:
--   For a strictly positive exponent a, the geometric reciprocal of the unit-discount resolvent equals one plus the undiscounted resolvent.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact reduction of 236fd4ab-a605-4b79-a83b-a3aaf7704a5b.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalResolventScalarIdentity
    (a : Real) (ha : 0 < a) :
    (1 - (ENNReal.ofReal (1 + a))⁻¹)⁻¹ =
      1 + (ENNReal.ofReal a)⁻¹ := by sorry
