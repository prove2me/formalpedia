-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_eventually_zero_of_subset
-- name    : GlobalTheory.InjHol.eventually_zero_of_subset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:00.147802+00:00
-- url     : https://prove2.me/theorems/3e38f512-07d2-4048-b280-c26fa70bf5a6
-- title:
--   Inj Hol: eventually zero of subset
-- statement:
--   The Inj Hol construction uses the eventually zero of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L141-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L141-L189

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
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

theorem GlobalTheory.InjHol.eventually_zero_of_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {g h : E → ℂ} {b : E} (hg : AnalyticAt ℂ g b) (hh : AnalyticAt ℂ h b)
    (h0 : fderiv ℂ g b ≠ 0) (hb : h b = 0) (hsub : ∀ᶠ z in 𝓝 b, h z = 0 → g z = 0) :
    ∀ᶠ z in 𝓝 b, g z = 0 → h z = 0 := by sorry
