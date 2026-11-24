-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_equiv_cmType_realEmbeddings_maxRealSubfield
-- name    : GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:33:43.979107+00:00
-- url     : https://prove2.me/theorems/83d0877c-f921-4728-9593-25480b119885
-- title:
--   T: exists equiv cm Type real Embeddings max Real Subfield
-- statement:
--   The T construction uses the exists equiv cm Type real Embeddings max Real Subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ) := by sorry
