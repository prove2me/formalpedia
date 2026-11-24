-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_exists_regular_of_zero
-- name    : GlobalTheory.InjHol.exists_regular_of_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:19.623402+00:00
-- url     : https://prove2.me/theorems/dcaf843b-e287-42b3-b81f-a755572d8630
-- title:
--   Inj Hol: exists regular of zero
-- statement:
--   The Inj Hol construction uses the exists regular of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L191-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L191-L232

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

theorem GlobalTheory.InjHol.exists_regular_of_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {h : E → ℂ} {a : E} (hh : AnalyticAt ℂ h a) (ha : h a = 0) (hne : ¬ ∀ᶠ z in 𝓝 a, h z = 0)
    {W : Set E} (hW : W ∈ 𝓝 a) :
    ∃ b ∈ W, h b = 0 ∧ AnalyticAt ℂ h b ∧ ∃ g : E → ℂ, AnalyticAt ℂ g b ∧ fderiv ℂ g b ≠ 0 ∧
      ∀ᶠ z in 𝓝 b, h z = 0 → g z = 0 := by sorry
