-- Prove2me | Theorems.Thm_GlobalTheory_idempotent_eq_of_basicOpen_eq
-- name    : GlobalTheory.idempotent_eq_of_basicOpen_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:47.65099+00:00
-- url     : https://prove2.me/theorems/9b594b88-42ee-4e7c-9beb-5d26d2c7e8c4
-- title:
--   Global Theory: idempotent eq of basic Open eq
-- statement:
--   The Global Theory construction uses the idempotent eq of basic Open eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentEqOfBasicOpenEq.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentEqOfBasicOpenEq.lean#L24-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
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

theorem GlobalTheory.idempotent_eq_of_basicOpen_eq : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' →
    X.basicOpen e = X.basicOpen e' → e = e' := by sorry
