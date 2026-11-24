-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_EmbClosed_isClosedEmbedding_emb
-- name    : GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:38.784552+00:00
-- url     : https://prove2.me/theorems/d298e391-5a5c-4052-a7ca-eaa3784c9454
-- title:
--   Emb Closed: is Closed Embedding emb
-- statement:
--   The Emb Closed construction uses the is Closed Embedding emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L26-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneGeneralLinearEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.EmbClosed

theorem GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb (F : Type) [NontriviallyNormedField F] (r : ℕ) :
    IsClosedEmbedding (emb r F) := by sorry
