-- Prove2me | Theorems.Thm_GlobalTheory_T_im_embedding_ne_zero_of_not_mem_range_algebraMap
-- name    : GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:47.72186+00:00
-- url     : https://prove2.me/theorems/d00aed54-3dae-48a3-8abb-66012d679107
-- title:
--   T: im embedding ne zero of not mem range algebra Map
-- statement:
--   The T construction uses the im embedding ne zero of not mem range algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadrStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadrStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 := by sorry
