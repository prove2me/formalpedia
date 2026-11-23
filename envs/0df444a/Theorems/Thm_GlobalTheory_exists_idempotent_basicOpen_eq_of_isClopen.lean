-- Prove2me | Theorems.Thm_GlobalTheory_exists_idempotent_basicOpen_eq_of_isClopen
-- name    : GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:42.290501+00:00
-- url     : https://prove2.me/theorems/a2583614-1d82-45fe-896e-24a841c7064d
-- title:
--   Global Theory: exists idempotent basic Open eq of is Clopen
-- statement:
--   The Global Theory construction uses the exists idempotent basic Open eq of is Clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdempotentOfClopen.lean#L6-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdempotentOfClopen.lean#L6-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory

theorem GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen :
    ∀ (X : Scheme.{0}) (U : Set X), IsClopen U →
      ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by sorry
