-- Prove2me | Theorems.Thm_MeasurableSelection_approxFun_measurable
-- name    : MeasurableSelection.approxFun_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:27.096801+00:00
-- url     : https://prove2.me/theorems/1345c20b-1d30-5c4b-a7db-6d823639e0fa
-- title:
--   Measurable Selection: approx Fun measurable
-- statement:
--   The Measurable Selection construction uses the approx Fun measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L193-L197
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L193-L197

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}

theorem MeasurableSelection.approxFun_measurable [MeasurableSpace Y] (hu : DenseRange u)
    (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) (n : ℕ) :
    Measurable (approxFun hu hne hΦ n) := by sorry
