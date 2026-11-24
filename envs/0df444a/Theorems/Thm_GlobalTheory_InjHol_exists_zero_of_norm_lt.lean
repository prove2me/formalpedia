-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_exists_zero_of_norm_lt
-- name    : GlobalTheory.InjHol.exists_zero_of_norm_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:47.963057+00:00
-- url     : https://prove2.me/theorems/0a25cfec-11a5-4ec8-90a1-632d80de0960
-- title:
--   Inj Hol: exists zero of norm lt
-- statement:
--   The Inj Hol construction uses the exists zero of norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L10-L25

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

theorem GlobalTheory.InjHol.exists_zero_of_norm_lt {φ : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (closedBall c r)) (h : ∀ t ∈ sphere c r, ‖φ c‖ < ‖φ t‖) :
    ∃ t ∈ closedBall c r, φ t = 0 := by sorry
