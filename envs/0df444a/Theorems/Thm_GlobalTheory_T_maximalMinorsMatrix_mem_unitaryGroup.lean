-- Prove2me | Theorems.Thm_GlobalTheory_T_maximalMinorsMatrix_mem_unitaryGroup
-- name    : GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:29.190876+00:00
-- url     : https://prove2.me/theorems/6aceef9c-1b76-4d12-8dcd-1fee78eb7705
-- title:
--   T: maximal Minors Matrix mem unitary Group
-- statement:
--   The T construction uses the maximal Minors Matrix mem unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalMinorsMatrixMemUnitaryGroupStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalMinorsMatrixMemUnitaryGroupStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroupStatement
import Theorems.Thm_GlobalTheory_IsLogBounded_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ), M ∈ Matrix.unitaryGroup (Fin N) ℂ → (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} => (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈ Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by sorry
