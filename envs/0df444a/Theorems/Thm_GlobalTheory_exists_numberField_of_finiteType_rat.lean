-- Prove2me | Theorems.Thm_GlobalTheory_exists_numberField_of_finiteType_rat
-- name    : GlobalTheory.exists_numberField_of_finiteType_rat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:13.440799+00:00
-- url     : https://prove2.me/theorems/fd2e7c9a-b2db-4304-824d-ba458e37b559
-- title:
--   Global Theory: exists number Field of finite Type rat
-- statement:
--   The Global Theory construction uses the exists number Field of finite Type rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeToNumberField.lean#L6-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeToNumberField.lean#L6-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeToNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory

theorem GlobalTheory.exists_numberField_of_finiteType_rat (R : Type) [CommRing R] [Nontrivial R] [Algebra ℚ R]
    [Algebra.FiniteType ℚ R] : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (φ : R →+* K), True := by sorry
