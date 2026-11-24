-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLift_embHom_apply_cc
-- name    : GlobalTheory.JR.GLift.embHom_apply_cc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:31:51.006205+00:00
-- url     : https://prove2.me/theorems/e67f6c7a-29e0-43b2-bafd-5bc2aab5b8ce
-- title:
--   GLift: emb Hom apply cc
-- statement:
--   The GLift construction uses the emb Hom apply cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PreimageDiagOneGeneralLinearEmbeddingIntegralGLS.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PreimageDiagOneGeneralLinearEmbeddingIntegralGLS.lean#L8-L10

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

theorem GlobalTheory.JR.GLift.embHom_apply_cc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.castSucc j) = a i j := by sorry
