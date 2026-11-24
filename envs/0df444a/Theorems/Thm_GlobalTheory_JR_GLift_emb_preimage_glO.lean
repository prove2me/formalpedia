-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLift_emb_preimage_glO
-- name    : GlobalTheory.JR.GLift.emb_preimage_glO
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:31:32.9905+00:00
-- url     : https://prove2.me/theorems/52faf071-71b5-44f6-ba50-9829fb7cd647
-- title:
--   GLift: emb preimage gl O
-- statement:
--   The GLift construction uses the emb preimage gl O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PreimageDiagOneGeneralLinearEmbeddingIntegralGLS.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PreimageDiagOneGeneralLinearEmbeddingIntegralGLS.lean#L33-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PreimageDiagOneGeneralLinearEmbeddingIntegralGLS
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift

theorem GlobalTheory.JR.GLift.emb_preimage_glO : ∀ (F : Type) [NormedField F] (r : ℕ),
    ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by sorry
