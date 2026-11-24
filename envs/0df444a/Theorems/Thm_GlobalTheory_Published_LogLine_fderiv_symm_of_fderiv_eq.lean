-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_fderiv_symm_of_fderiv_eq
-- name    : GlobalTheory.Published.LogLine.fderiv_symm_of_fderiv_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:56:48.301569+00:00
-- url     : https://prove2.me/theorems/5dddfeff-21cf-4ae0-a5f5-abdfebeff1f8
-- title:
--   Log Line: fderiv symm of fderiv eq
-- statement:
--   The Log Line construction uses the fderiv symm of fderiv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L214-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L214-L231

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

theorem GlobalTheory.Published.LogLine.fderiv_symm_of_fderiv_eq {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {β : (Fin n → ℂ) → (Fin n → ℂ) →L[ℂ] ℂ} {f : (Fin n → ℂ) → ℂ}
    (hβ : DifferentiableOn ℂ β V) (hf : DifferentiableOn ℂ f V) (hne : ∀ z ∈ V, f z ≠ 0)
    (h : ∀ z ∈ V, fderiv ℂ f z = -(f z • β z)) {z : Fin n → ℂ} (hz : z ∈ V) (x y : Fin n → ℂ) :
    fderiv ℂ β z x y = fderiv ℂ β z y x := by sorry
