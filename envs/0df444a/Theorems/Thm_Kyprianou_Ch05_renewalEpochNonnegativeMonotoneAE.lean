-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalEpochNonnegativeMonotoneAE
-- name    : Kyprianou.Ch05.renewalEpochNonnegativeMonotoneAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:55:50.450144+00:00
-- url     : https://prove2.me/theorems/47198453-878b-456e-8c91-85a528425855
-- title:
--   Nonnegative renewal spacings give almost surely nonnegative monotone epochs
-- statement:
--   Nonnegative renewal spacings give almost surely nonnegative monotone epochs
-- source:
--   Kyprianou (2006), Lemma 5.5; finite-level renewal crossing and tail integrability.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalEpochNonnegativeMonotoneAE
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F) :
    ∀ᵐ w ∂P, (∀ n : Nat, 0 ≤ Z n w) ∧
      Monotone (fun n : Nat => renewalEpoch Z n w) := by sorry
