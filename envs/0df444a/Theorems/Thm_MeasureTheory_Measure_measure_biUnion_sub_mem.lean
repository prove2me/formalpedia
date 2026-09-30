-- Prove2me | Theorems.Thm_MeasureTheory_Measure_measure_biUnion_sub_mem
-- name    : MeasureTheory.Measure.measure_biUnion_sub_mem
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:32:19.909775+00:00
-- url     : https://prove2.me/theorems/7729b876-5bf9-4f72-af0d-680390d71f25
-- title:
--   Measure of finitely many disjoint translates
-- statement:
--   Let $E$ be an additive group with a measurable structure and measurable addition, and let $\mu$ be a right-translation-invariant measure. Let $F\subseteq E$ be measurable and suppose its translates $F+w$ for $w$ in a set $A$ are pairwise disjoint. For every finite subset $T\subseteq A$,
--
--   $$
--   \mu\!\left(\bigcup_{w\in T}(F+w)\right)=|T|\,\mu(F).
--   $$
--
--   This computes the measure of a finite disjoint family of congruent measurable pieces, without assuming finite measure.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/MeasureTheory/Group/Measure.lean#L31-L53), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/MeasureTheory/Group/Measure.lean#L31-L53

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.MeasureTheory.Group.Measure

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Measures invariant under addition

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
-/

 section

open MeasureTheory Set

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

theorem MeasureTheory.Measure.measure_biUnion_sub_mem
    (mu : _root_.MeasureTheory.Measure E) [mu.IsAddRightInvariant]
    {G F : _root_.Set E} (hFm : _root_.MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      _root_.Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : _root_.Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by sorry
