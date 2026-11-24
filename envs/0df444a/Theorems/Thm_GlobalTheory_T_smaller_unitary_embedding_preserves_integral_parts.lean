-- Prove2me | Theorems.Thm_GlobalTheory_T_smaller_unitary_embedding_preserves_integral_parts
-- name    : GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:41.281022+00:00
-- url     : https://prove2.me/theorems/6fc8058e-f40c-4088-8ebe-3e17efa5bd79
-- title:
--   T: smaller unitary embedding preserves integral parts
-- statement:
--   The T construction uses the smaller unitary embedding preserves integral parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmallerUnitaryEmbeddingPreservesIntegralPartsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmallerUnitaryEmbeddingPreservesIntegralPartsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallerUnitaryEmbeddingPreservesIntegralParts
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallerUnitaryEmbeddingPreservesIntegralPartsStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts : GlobalTheory.SatakeWeyl.EmbMem := by sorry
