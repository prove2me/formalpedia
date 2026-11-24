-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_exists_ball_div
-- name    : GlobalTheory.Published.LogLine.exists_ball_div
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:56:35.012004+00:00
-- url     : https://prove2.me/theorems/f2c17332-f297-41a5-b4dd-2728542aaeaa
-- title:
--   Log Line: exists ball div
-- statement:
--   The Log Line construction uses the exists ball div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L168-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L168-L196

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

theorem GlobalTheory.Published.LogLine.exists_ball_div {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n))
    {a : Fin n → (Fin n → ℂ) → ℂ} (ha : ∀ i, DifferentiableOn ℂ (a i) U)
    (h0 : ∀ i ∈ S, ∀ z ∈ U, z i = 0 → a i z = 0) {c : Fin n → ℂ} (hc : c ∈ U) :
    ∃ r > 0, ball c r ⊆ U ∧ ∃ b : Fin n → (Fin n → ℂ) → ℂ,
      (∀ i, DifferentiableOn ℂ (b i) (ball c r)) ∧
      ∀ i, ∀ z ∈ ball c r, a i z = (if i ∈ S then z i else 1) * b i z := by sorry
