-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Hgt_count_grp
-- name    : GlobalTheory.ThK.Dbl.Hgt.count_grp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:27.240727+00:00
-- url     : https://prove2.me/theorems/69217130-b3f3-4b80-9463-3c170d230ff0
-- title:
--   Hgt: count grp
-- statement:
--   The Hgt construction uses the count grp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HgtCount.lean#L77-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HgtCount.lean#L77-L112

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

theorem GlobalTheory.ThK.Dbl.Hgt.count_grp {R B κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Ring B] [Algebra R B] [TopologicalSpace B]
    [IsTopologicalRing B] [T2Space B] [Fintype κ] (c : B ≃ₗ[R] (κ → R)) (hc : Continuous c) (hc' : Continuous c.symm)
    (H : Subgroup Bˣ) (hH : IsClosed (H : Set Bˣ)) {Ω : Set B} (hΩ : IsCompact Ω) {W : Set R} (hW : IsCompact W) :
    ∃ (X : Set R) (U : Set H), IsCompact X ∧ IsCompact U ∧ ∀ (l : Rˣ) (s : Finset R),
      (∀ x ∈ X, ∃ y ∈ s, ∃ w ∈ W, x - y = l * l * w) → ∀ [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant],
        μ {g | l.1 • g.1.1 ∈ Ω ∧ l.1 • (g⁻¹).1.1 ∈ Ω} ≤ (s.card : ℝ≥0∞) ^ Fintype.card κ * μ U := by sorry
