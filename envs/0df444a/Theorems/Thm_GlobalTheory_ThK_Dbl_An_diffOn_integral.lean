-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_An_diffOn_integral
-- name    : GlobalTheory.ThK.Dbl.An.diffOn_integral
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:45.046861+00:00
-- url     : https://prove2.me/theorems/9542869f-e170-474d-af5a-8e311bb609c0
-- title:
--   An: diff On integral
-- statement:
--   The An construction uses the diff On integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/UnfoldA.lean#L17-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/UnfoldA.lean#L17-L44

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_UnfoldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology

theorem GlobalTheory.ThK.Dbl.An.diffOn_integral {X : Type} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {k : ℂ → X → ℂ} (hm : ∀ s ∈ U, AEStronglyMeasurable (k s) μ) (hd : ∀ x, DifferentiableOn ℂ (k · x) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ s ∈ K, ∀ x, ‖k s x‖ ≤ C) :
    DifferentiableOn ℂ (fun s => ∫ x, k s x ∂μ) U := by sorry
