-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_EmbClosed_continuous_embHom
-- name    : GlobalTheory.JR.Step.EmbClosed.continuous_embHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:36:15.24496+00:00
-- url     : https://prove2.me/theorems/920a4c93-8e1c-455e-8c83-a6a409126fd7
-- title:
--   Emb Closed: continuous emb Hom
-- statement:
--   The Emb Closed construction uses the continuous emb Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L12-L17

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

theorem GlobalTheory.JR.Step.EmbClosed.continuous_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    Continuous (embHom r F) := by sorry
