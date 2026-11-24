-- Prove2me | Theorems.Thm_GlobalTheory_AnalyticMatrixEntries_analyticAt_det
-- name    : GlobalTheory.AnalyticMatrixEntries.analyticAt_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:35.171608+00:00
-- url     : https://prove2.me/theorems/bfbc4cfc-0fdc-4711-99bb-861f0725585c
-- title:
--   Analytic Matrix Entries: analytic At det
-- statement:
--   The Analytic Matrix Entries construction uses the analytic At det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtEntry.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtEntry.lean#L19-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticMatrixEntries
universe u_1 u_2

theorem GlobalTheory.AnalyticMatrixEntries.analyticAt_det {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : X → E →L[ℂ] E} {a : X} (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z : X ↦ LinearMap.det (A z : E →ₗ[ℂ] E)) a := by sorry
