-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_analyticAt_det
-- name    : GlobalTheory.InjHol.analyticAt_det
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:29.860502+00:00
-- url     : https://prove2.me/theorems/20533587-6aae-4d0c-bd47-df2287ae9909
-- title:
--   Inj Hol: analytic At det
-- statement:
--   The Inj Hol construction uses the analytic At det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L234-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L234-L244

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_AnalyticMatrixEntries_analyticAt_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol

theorem GlobalTheory.InjHol.analyticAt_det {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z => LinearMap.det (A z : E →ₗ[ℂ] E)) a := by sorry
