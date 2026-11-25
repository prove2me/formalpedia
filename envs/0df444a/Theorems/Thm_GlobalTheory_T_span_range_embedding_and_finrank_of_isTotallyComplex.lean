-- Prove2me | Theorems.Thm_GlobalTheory_T_span_range_embedding_and_finrank_of_isTotallyComplex
-- name    : GlobalTheory.T.span_range_embedding_and_finrank_of_isTotallyComplex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:40.931816+00:00
-- url     : https://prove2.me/theorems/d8beed78-ca9e-4e79-a651-8327a3f1c9e7
-- title:
--   T: span range embedding and finrank of is Totally Complex
-- statement:
--   The T construction uses the span range embedding and finrank of is Totally Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TotallyComplexSpanEmbeddingsAndFinrankStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TotallyComplexSpanEmbeddingsAndFinrankStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TotallyComplexSpanEmbeddingsAndFinrank
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TotallyComplexSpanEmbeddingsAndFinrankStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.span_range_embedding_and_finrank_of_isTotallyComplex : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], Submodule.span ℝ (Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding)) = ⊤ ∧ Module.finrank ℝ (InfinitePlace E → ℂ) = Module.finrank ℚ E := by sorry
