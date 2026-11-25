-- Prove2me | Theorems.Thm_GlobalTheory_absNorm_map_ringEquiv_self
-- name    : GlobalTheory.absNorm_map_ringEquiv_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:42.442902+00:00
-- url     : https://prove2.me/theorems/c46bed07-8589-40ad-bd90-baa73f98cf5c
-- title:
--   Global Theory: abs Norm map ring Equiv self
-- statement:
--   The Global Theory construction uses the abs Norm map ring Equiv self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/AbsNormSqOfMulConjEqDifferentIdeal.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/AbsNormSqOfMulConjEqDifferentIdeal.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AbsNormSqOfMulConjEqDifferentIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real NumberField
open GlobalTheory

theorem GlobalTheory.absNorm_map_ringEquiv_self {R : Type} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] (e : R ≃+* R) (J : Ideal R) :
    Ideal.absNorm (J.map e.toRingHom) = Ideal.absNorm J := by sorry
