-- Prove2me | Theorems.Thm_GlobalTheory_Div_CMAlgChar_embedding_ne_conjugate
-- name    : GlobalTheory.Div.CMAlgChar.embedding_ne_conjugate
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:50:41.993684+00:00
-- url     : https://prove2.me/theorems/6176ecbb-dcd6-445e-86ab-df5f5a440a99
-- title:
--   CMAlg Char: embedding ne conjugate
-- statement:
--   The CMAlg Char construction uses the embedding ne conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbs.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbs.lean#L46-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.CMAlgChar

theorem GlobalTheory.Div.CMAlgChar.embedding_ne_conjugate {E : Type} [Field E] [IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by sorry
