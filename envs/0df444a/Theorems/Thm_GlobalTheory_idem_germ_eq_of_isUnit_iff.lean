-- Prove2me | Theorems.Thm_GlobalTheory_idem_germ_eq_of_isUnit_iff
-- name    : GlobalTheory.idem_germ_eq_of_isUnit_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:32.506925+00:00
-- url     : https://prove2.me/theorems/a7cbc405-a4e5-419a-839f-ef4e50d58177
-- title:
--   Global Theory: idem germ eq of is Unit iff
-- statement:
--   The Global Theory construction uses the idem germ eq of is Unit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentEqOfBasicOpenEq.lean#L6-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentEqOfBasicOpenEq.lean#L6-L22

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

theorem GlobalTheory.idem_germ_eq_of_isUnit_iff {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : a * a = a) (hb : b * b = b) (h : IsUnit a ↔ IsUnit b) : a = b := by sorry
