-- Prove2me | Theorems.Thm_GlobalTheory_DenseEmbeddingProduct_denseRange_embedding_pi
-- name    : GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:23.312808+00:00
-- url     : https://prove2.me/theorems/1167c05f-7e7d-400d-b02d-41782e5f24ea
-- title:
--   Dense Embedding Product: dense Range embedding pi
-- statement:
--   The Dense Embedding Product construction uses the dense Range embedding pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DenseRangeEmbeddingPi.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DenseRangeEmbeddingPi.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DenseRangeEmbeddingPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DenseEmbeddingProduct
open NumberField NumberField.InfinitePlace

theorem GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DenseRange fun (x : E) (w : InfinitePlace E) ↦ (InfinitePlace.embedding w : E → ℂ) x := by sorry
