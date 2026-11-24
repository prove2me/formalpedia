-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_An_unfold
-- name    : GlobalTheory.ThK.Dbl.An.unfold
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:34:43.222108+00:00
-- url     : https://prove2.me/theorems/dbfd6cd8-c67d-4369-b91a-b3f62ed4ea7b
-- title:
--   An: unfold
-- statement:
--   The An construction uses the unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/UnfoldA.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/UnfoldA.lean#L9-L15

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

theorem GlobalTheory.ThK.Dbl.An.unfold {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {f : G → ℂ} (hf : Integrable f μ) : ∫ x in D, ∑' γ : Γ, f (γ * x) ∂μ = ∫ x, f x ∂μ := by sorry
