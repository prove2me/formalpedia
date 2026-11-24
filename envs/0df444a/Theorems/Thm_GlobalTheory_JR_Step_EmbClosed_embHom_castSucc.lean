-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_EmbClosed_embHom_castSucc
-- name    : GlobalTheory.JR.Step.EmbClosed.embHom_castSucc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:53.534592+00:00
-- url     : https://prove2.me/theorems/7167cfd7-8a95-478b-aa59-b5d67a650cbe
-- title:
--   Emb Closed: emb Hom cast Succ
-- statement:
--   The Emb Closed construction uses the emb Hom cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneGeneralLinearEmbedding.lean#L8-L10

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

theorem GlobalTheory.JR.Step.EmbClosed.embHom_castSucc {r : ℕ} {k : Type} [CommRing k] (g : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    embHom r k g (Fin.castSucc i) (Fin.castSucc j) = g i j := by sorry
