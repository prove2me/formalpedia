-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SplitUnramifiedPlaces_Place_conj_induces_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place.conj_induces_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:43.247187+00:00
-- url     : https://prove2.me/theorems/5f7eec6e-6824-4ec1-a721-84a7ba764bb1
-- title:
--   Place: conj induces iff
-- statement:
--   The Place construction uses the conj induces iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L84-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L84-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place
variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]

theorem GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place.conj_induces_iff [StarRing OE] (w : Place p OE) {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] (σ : OE →+* O) :
    w.conj.Induces σ ↔ w.Induces (σ.comp (starRingEnd OE)) := by sorry
