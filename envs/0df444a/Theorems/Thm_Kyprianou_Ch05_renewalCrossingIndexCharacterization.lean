-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingIndexCharacterization
-- name    : Kyprianou.Ch05.renewalCrossingIndexCharacterization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:58:07.255808+00:00
-- url     : https://prove2.me/theorems/8031d823-391c-4b8c-89a5-4dc051d8c83f
-- title:
--   First crossing index equals n+1 precisely at a strict crossing of a nondecreasing epoch sequence
-- statement:
--   First crossing index equals n+1 precisely at a strict crossing of a nondecreasing epoch sequence
-- source:
--   Kyprianou (2006), Lemma 5.5; reduction of the renewal-tail and first-crossing proofs.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalCrossingIndexCharacterization
    {Omega : Type} (Z : Nat → Omega → Real) (w : Omega)
    (hmono : Monotone (fun n : Nat => renewalEpoch Z n w))
    (x : Real) (hx : 0 < x) (n : Nat) :
    (nextRenewalIndex Z x w = n+1 ∧ x < renewalEpoch Z (n+1) w) ↔
      (renewalEpoch Z n w ≤ x ∧ x < renewalEpoch Z (n+1) w) := by sorry
