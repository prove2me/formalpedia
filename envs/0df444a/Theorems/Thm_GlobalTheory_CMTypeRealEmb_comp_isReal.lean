-- Prove2me | Theorems.Thm_GlobalTheory_CMTypeRealEmb_comp_isReal
-- name    : GlobalTheory.CMTypeRealEmb.comp_isReal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:04:28.836448+00:00
-- url     : https://prove2.me/theorems/01588916-c735-42bd-96b0-0682224f7b12
-- title:
--   CMType Real Emb: comp is Real
-- statement:
--   The CMType Real Emb construction uses the comp is Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield.lean#L7-L14

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
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
open GlobalTheory GlobalTheory.CMTypeRealEmb

theorem GlobalTheory.CMTypeRealEmb.comp_isReal {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap (maximalRealSubfield E) E)) := by sorry
