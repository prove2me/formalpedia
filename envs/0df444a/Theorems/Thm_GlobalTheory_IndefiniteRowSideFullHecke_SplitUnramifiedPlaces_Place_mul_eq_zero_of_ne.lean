-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SplitUnramifiedPlaces_Place_mul_eq_zero_of_ne
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place.mul_eq_zero_of_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:38.99275+00:00
-- url     : https://prove2.me/theorems/22b2eda0-7fb9-485d-aeb5-65e40d5ae79b
-- title:
--   Place: mul eq zero of ne
-- statement:
--   The Place construction uses the mul eq zero of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L62-L68

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place.mul_eq_zero_of_ne {w u : Place p OE} (h : w ≠ u) : w.e * u.e = 0 := by sorry
