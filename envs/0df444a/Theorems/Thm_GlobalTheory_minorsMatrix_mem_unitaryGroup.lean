-- Prove2me | Theorems.Thm_GlobalTheory_minorsMatrix_mem_unitaryGroup
-- name    : GlobalTheory.minorsMatrix_mem_unitaryGroup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:42.507049+00:00
-- url     : https://prove2.me/theorems/cc8430ee-401d-45dd-974c-3f79ff1bd77e
-- title:
--   Global Theory: minors Matrix mem unitary Group
-- statement:
--   The Global Theory construction uses the minors Matrix mem unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalMinorsMatrixMemUnitaryGroup.lean#L24-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalMinorsMatrixMemUnitaryGroup.lean#L24-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup
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
open GlobalTheory

theorem GlobalTheory.minorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ),
    M ∈ Matrix.unitaryGroup (Fin N) ℂ →
    (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈
      Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by sorry
