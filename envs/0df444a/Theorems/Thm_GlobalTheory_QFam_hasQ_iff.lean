-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_iff
-- name    : GlobalTheory.QFam.hasQ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:23.437+00:00
-- url     : https://prove2.me/theorems/e9c74acd-de82-4b28-89bc-971bc8fa62d8
-- title:
--   QFam: has Q iff
-- statement:
--   The QFam construction uses the has Q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HasQIff.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HasQIff.lean#L55-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups ModularForm
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.hasQ_iff (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n) (f τ) := by sorry
