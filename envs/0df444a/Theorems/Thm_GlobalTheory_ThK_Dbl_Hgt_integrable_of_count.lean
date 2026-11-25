-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Hgt_integrable_of_count
-- name    : GlobalTheory.ThK.Dbl.Hgt.integrable_of_count
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:11.939132+00:00
-- url     : https://prove2.me/theorems/de26cb72-3b30-4559-8fec-ca16cb8ee364
-- title:
--   Hgt: integrable of count
-- statement:
--   The Hgt construction uses the integrable of count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HgtCount.lean#L36-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HgtCount.lean#L36-L75

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HgtCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Hgt
open scoped NNReal ENNReal
open MeasureTheory Topology

theorem GlobalTheory.ThK.Dbl.Hgt.integrable_of_count {G : Type} [MeasurableSpace G] (μ : Measure G) {f : G → ℝ} (hf : Measurable f) (h0 : ∀ g, 0 < f g)
    {R : ℝ} (h1 : 1 ≤ R) (hR : ∀ g, f g ≤ R) {C : ℝ≥0∞} (hC : C ≠ ⊤) (b : ℝ≥0)
    (h : ∀ j : ℕ, μ {g | (1 / 2) ^ j ≤ f g} ≤ C * b ^ j) : ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => f g ^ t) μ := by sorry
