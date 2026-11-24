-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_exists_div_ball
-- name    : GlobalTheory.Published.LogLine.exists_div_ball
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:56:51.657159+00:00
-- url     : https://prove2.me/theorems/6c992d8f-2bb9-4958-82cc-65a955e7b73b
-- title:
--   Log Line: exists div ball
-- statement:
--   The Log Line construction uses the exists div ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L118-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L118-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}

theorem GlobalTheory.Published.LogLine.exists_div_ball {a : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} {i : Fin n} (hc : c i = 0)
    (ha : DifferentiableOn ℂ a (ball c r)) (h0 : ∀ z ∈ ball c r, z i = 0 → a z = 0) :
    ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b (ball c r) ∧ ∀ z ∈ ball c r, a z = z i * b z := by sorry
