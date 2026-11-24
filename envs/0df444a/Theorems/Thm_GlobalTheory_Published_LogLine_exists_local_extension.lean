-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_exists_local_extension
-- name    : GlobalTheory.Published.LogLine.exists_local_extension
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:56:58.050729+00:00
-- url     : https://prove2.me/theorems/bbdc8099-ebbc-4ab3-98e6-52393800e949
-- title:
--   Log Line: exists local extension
-- statement:
--   The Log Line construction uses the exists local extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L233-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L233-L279

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

theorem GlobalTheory.Published.LogLine.exists_local_extension {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (S : Finset (Fin n))
    {b : Fin n → (Fin n → ℂ) → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) (ball c r))
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (offDivisor (ball c r) S))
    (hne : ∀ z ∈ offDivisor (ball c r) S, f z ≠ 0)
    (h : ∀ z ∈ offDivisor (ball c r) S, ∀ i, fderiv ℂ f z (Pi.single i 1) = -(f z * b i z)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (ball c r) ∧
      EqOn F f (offDivisor (ball c r) S) ∧ ∀ z ∈ ball c r, F z ≠ 0 := by sorry
