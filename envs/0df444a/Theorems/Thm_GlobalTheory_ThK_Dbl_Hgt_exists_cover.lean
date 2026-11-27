-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Hgt_exists_cover
-- name    : GlobalTheory.ThK.Dbl.Hgt.exists_cover
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:08.135243+00:00
-- url     : https://prove2.me/theorems/bcedff24-cf3c-5bfa-87c2-5fe6f8d055ee
-- title:
--   Hgt: exists cover
-- statement:
--   The Hgt construction uses the exists cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HgtCount.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HgtCount.lean#L10-L34

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

theorem GlobalTheory.ThK.Dbl.Hgt.exists_cover {A : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (ν : Measure A) [ν.IsAddLeftInvariant]
    {X V Z : Set A} (hV : MeasurableSet V) (h0 : ν V ≠ 0) (hZ : ν Z ≠ ⊤) (hXZ : ∀ x ∈ X, ∀ v ∈ V, x + v ∈ Z) :
    ∃ s : Finset A, s.card * ν V ≤ ν Z ∧ ∀ x ∈ X, ∃ y ∈ s, ∃ v ∈ V, ∃ v' ∈ V, x - y = v - v' := by sorry
