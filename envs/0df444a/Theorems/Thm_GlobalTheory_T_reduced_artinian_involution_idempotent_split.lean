-- Prove2me | Theorems.Thm_GlobalTheory_T_reduced_artinian_involution_idempotent_split
-- name    : GlobalTheory.T.reduced_artinian_involution_idempotent_split
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:31.417745+00:00
-- url     : https://prove2.me/theorems/54851319-f13b-4a3b-a66c-63a876c0d69e
-- title:
--   T: reduced artinian involution idempotent split
-- statement:
--   The T construction uses the reduced artinian involution idempotent split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReducedArtinianInvolutionIdempotentSplitStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReducedArtinianInvolutionIdempotentSplitStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReducedArtinianInvolutionIdempotentSplit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReducedArtinianInvolutionIdempotentSplitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.reduced_artinian_involution_idempotent_split : ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧ ∀ w, w * σ w = 0 → w * f = 0 := by sorry
