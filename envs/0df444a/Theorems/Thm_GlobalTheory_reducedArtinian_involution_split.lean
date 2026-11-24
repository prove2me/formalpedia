-- Prove2me | Theorems.Thm_GlobalTheory_reducedArtinian_involution_split
-- name    : GlobalTheory.reducedArtinian_involution_split
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:22.291812+00:00
-- url     : https://prove2.me/theorems/5ded6fab-a6b9-4362-b470-c2ed92765df7
-- title:
--   Global Theory: reduced Artinian involution split
-- statement:
--   The Global Theory construction uses the reduced Artinian involution split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReducedArtinianInvolutionIdempotentSplit.lean#L26-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReducedArtinianInvolutionIdempotentSplit.lean#L26-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReducedArtinianInvolutionIdempotentSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory

theorem GlobalTheory.reducedArtinian_involution_split :
    ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
      ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧
        ∀ w, w * σ w = 0 → w * f = 0 := by sorry
