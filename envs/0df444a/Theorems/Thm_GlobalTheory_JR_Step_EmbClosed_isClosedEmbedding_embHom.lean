-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_EmbClosed_isClosedEmbedding_embHom
-- name    : GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_embHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:52.599588+00:00
-- url     : https://prove2.me/theorems/ab26f844-772a-4b70-ba2c-ba7a0e8359a2
-- title:
--   Emb Closed: is Closed Embedding emb Hom
-- statement:
--   The Emb Closed construction uses the is Closed Embedding emb Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L19-L24

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

theorem GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    IsClosedEmbedding (embHom r F) := by sorry
