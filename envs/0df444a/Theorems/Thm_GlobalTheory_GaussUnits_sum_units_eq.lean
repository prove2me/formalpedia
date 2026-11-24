-- Prove2me | Theorems.Thm_GlobalTheory_GaussUnits_sum_units_eq
-- name    : GlobalTheory.GaussUnits.sum_units_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:08.963708+00:00
-- url     : https://prove2.me/theorems/048889d7-2e8b-4e0b-92c9-0c38cec5391a
-- title:
--   Gauss Units: sum units eq
-- statement:
--   The Gauss Units construction uses the sum units eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussUnitsNormSq.lean#L47-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussUnitsNormSq.lean#L47-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussUnitsNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ComplexConjugate Finset
open GlobalTheory
open GlobalTheory.GaussUnits
variable {R : Type} [CommRing R] [Fintype R]

theorem GlobalTheory.GaussUnits.sum_units_eq (m : Ideal R) [DecidablePred (· ∈ m)] [Fintype Rˣ]
    (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (f : R → ℂ) :
    ∑ u : Rˣ, f u = ∑ x, f x - ∑ x, (if x ∈ m then f x else 0) := by sorry
