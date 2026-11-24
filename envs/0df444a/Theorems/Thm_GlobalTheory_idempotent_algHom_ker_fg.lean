-- Prove2me | Theorems.Thm_GlobalTheory_idempotent_algHom_ker_fg
-- name    : GlobalTheory.idempotent_algHom_ker_fg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:53.239544+00:00
-- url     : https://prove2.me/theorems/a5ee930b-d8db-4dd1-937a-91574a727bea
-- title:
--   Global Theory: idempotent alg Hom ker fg
-- statement:
--   The Global Theory construction uses the idempotent alg Hom ker fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothRangeOfIdempotentAlgHom.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothRangeOfIdempotentAlgHom.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothRangeOfIdempotentAlgHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.idempotent_algHom_ker_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (e : A →ₐ[R] A) (he : ∀ x, e (e x) = e x) :
    (RingHom.ker e.rangeRestrict.toRingHom).FG := by sorry
