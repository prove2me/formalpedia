-- Prove2me | Theorems.Thm_GlobalTheory_reducedArtinian_exists_idem
-- name    : GlobalTheory.reducedArtinian_exists_idem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:15.069203+00:00
-- url     : https://prove2.me/theorems/de72ded7-9324-463f-bf44-5252330215aa
-- title:
--   Global Theory: reduced Artinian exists idem
-- statement:
--   The Global Theory construction uses the reduced Artinian exists idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReducedArtinianInvolutionIdempotentSplit.lean#L6-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReducedArtinianInvolutionIdempotentSplit.lean#L6-L24

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

theorem GlobalTheory.reducedArtinian_exists_idem {R : Type} [CommRing R] [IsReduced R] [IsArtinianRing R]
    (a : R) : ∃ e b : R, e * e = e ∧ e = a * b ∧ a * e = a := by sorry
