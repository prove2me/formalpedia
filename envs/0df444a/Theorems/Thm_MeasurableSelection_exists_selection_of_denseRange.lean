-- Prove2me | Theorems.Thm_MeasurableSelection_exists_selection_of_denseRange
-- name    : MeasurableSelection.exists_selection_of_denseRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:45.076215+00:00
-- url     : https://prove2.me/theorems/385b223b-3171-4a69-aa87-5d768fd6b00a
-- title:
--   Measurable Selection: exists selection of dense Range
-- statement:
--   Main construction, given a dense sequence: the approximations form a uniformly
--   Cauchy sequence; the pointwise limit is a measurable selection of `Φ`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L205-L233
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L205-L233

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}
variable [MeasurableSpace Y] [BorelSpace Y]

theorem MeasurableSelection.exists_selection_of_denseRange [CompleteSpace Y]
    (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) (hclosed : ∀ a, IsClosed (Φ a))
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a := by sorry
